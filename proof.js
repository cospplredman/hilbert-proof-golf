let PF = {
	mp: 4,
	a1: 5,
	a2: 6,
	a3: 7,
	line: 8,
	proof: 9
};

let MP = (a, b) => ({type: PF.mp, a, b});
let A1 = (a, b) => ({type: PF.a1, a, b});
let A2 = (a, b, c) => ({type: PF.a2, a, b, c});
let A3 = (a, b) => ({type: PF.a3, a, b});

let Line = (label, rule) => ({type: PF.line, label, rule});
let Proof = (lines) => ({type: PF.proof, lines});


let check = (pf) => {
	if(pf.type == PF.proof){
		let lines = {};
		let lookup = (label) => {
			if(lines[label] == null)
				throw new Error(label + " is not defined");

			return lines[label];
		}

		if(pf.lines.length == 0)
			throw new Error("you got this :)");

		pf.lines.forEach(v => {
			if(v.type == PF.line){
				if(lines[v.label] != null)
					throw new Error(v.label + " already defined");

				console.log(v, lines);
				let deduction;
				switch(v.rule.type){
					case PF.mp:
						deduction = mp(lookup(v.rule.a), lookup(v.rule.b));
					break;
					case PF.a1:
						deduction = a1(v.rule.a, v.rule.b);
					break;
					case PF.a2:
						deduction = a2(v.rule.a, v.rule.b, v.rule.c);
					break;
					case PF.a3:
						deduction = a3(v.rule.a, v.rule.b);
					break;
					default:
						throw new Error("expected a rule");
				}

				if(deduction == null)
					throw new Error(v.label + " is not a valid proof step");
				lines[v.label] = deduction;
				return;
			}

			throw new Error("expected a PF.line");
		});


		return lookup(pf.lines.at(-1).label);
	}

	throw new Error("expected a proof");
}



let log = (f, ...tag) => (...x) => (console.log(...tag, ...x), f(...x));
let State = (str, stack, index, new_lines, fail) => ({str, stack, index, new_lines, fail});
let IncState = (st) => State(st.str, st.stack, st.index + 1, st.new_lines + (st.str[st.index] == "\n"), st.fail);
let FailState = (st, nxt) => State(st.str, st.stack, st.index, st.new_lines, nxt);
let FailJoin = (st1, st2) => st1.index > st2.index ? st1 : st2;
let CurChar = (st) => st.str[st.index];
let PushStack = (v) => (nxt) => (st) => nxt(State(st.str, [...st.stack, v], st.index, st.new_lines, st.fail));
let PopStack = (f) => (nxt) => (st) => f(st.stack.at(-1))(nxt)(State(st.str, st.stack.slice(0, -1), st.index, st.new_lines, st.fail));


let Eq = (ch) => (nxt) => (st) => CurChar(st) == ch ? nxt(IncState(st)) : FailState(st, nxt);
let Rx = (rx) => (nxt) => (st) => rx.test(CurChar(st)) && CurChar(st) != null 
	? PushStack(CurChar(st))(nxt)(IncState(st))
	: FailState(st, nxt);

let Id = (nxt) => nxt;
let Fail = (nxt) => (st) => FailState(st, nxt);

let Both = (a, b) => (nxt) => a(b(nxt));
let Either = (a, b) => (nxt) => (st) => {
	let s1 = a(nxt)(st)
	if(s1.fail){
		let s2 = b(nxt)(st);
		if(s2.fail)
			return FailJoin(s1, s2);
		return s2;
	}

	return s1;
}

let all = (...xs) => xs.reduce(Both, Id);
let some = (...xs) => xs.reduce(Either, Fail);

let Many = (f) => (nxt) => st => {
	let arr = [];
	let call = (st) => all(f, PopStack(v => nxt => (arr.push(v), nxt)))(Id)(st);

	let ns = call(st);
	let ret = st;
	while(!ns.fail){
		ret = ns;
		ns = call(ns);
	}

	return PushStack(arr)(nxt)(ret);
};

let Del = PopStack(x => Id);
let Str = ([...ch]) => all(...ch.flatMap(Eq));
let Opt = (f) => Either(f, Id);

let wspace = Both(Many(Rx(/\s/)), Del);

let prop_grammar = (nxt) => {
	let ref = all(Rx(/[^->!\s\(\[\]\)]/), Many(Rx(/[^->!\s\(\[\]\)]/)), PopStack(arr => PopStack(v => PushStack(Ref([v, ...arr].join(""))))));

	let primary_expr = all(wspace, some(
		ref,
		all(Str("("), prop_grammar, wspace, Str(")")),
	));

	let not_expr = (nxt) => all(wspace, some(
		primary_expr,
		all(Str("!"), some(not_expr, primary_expr), 
		PopStack(v => PushStack(Not(v))))))(nxt);

	let arrow_expr = all(not_expr, 
		Many(all(wspace, Str("->"), not_expr)), 
		PopStack(arr => 
			PopStack(v => PushStack([v, ...arr].reduceRight((a, b) => Arrow(b, a))))));

	return arrow_expr(nxt);
}

let proof_grammar = (nxt) => {
	let label = all(Rx(/[a-z0-9]/), Many(Rx(/[a-z0-9]/)), PopStack(arr => PopStack(v => PushStack([v, ...arr].join("")))));

	let prop = all(wspace, Str("["), prop_grammar, wspace, Str("]"));

	let rule_mp = all(wspace, Str("MP"), wspace, label, wspace, label, 
		PopStack(arg => PopStack(func => PushStack(MP(func, arg)))));
	let rule_a1 = all(wspace, Str("A1"), prop, prop,
		PopStack(b => PopStack(a => PushStack(A1(a, b)))));
	let rule_a2 = all(wspace, Str("A2"), prop, prop, prop,
		PopStack(c => PopStack(b => PopStack(a => PushStack(A2(a, b, c))))));
	let rule_a3 = all(wspace, Str("A3"), prop, prop,
		PopStack(b => PopStack(a => PushStack(A3(a, b)))));

	let rule = some(rule_mp, rule_a1, rule_a2, rule_a3);

	let comment = all(wspace, Str("--"), Many(Rx(/[^\n]/)), Del, PushStack(null));
	let line = all(wspace, label, Str(":"), rule, wspace, Str(";"), 
		PopStack(rule => PopStack(label => PushStack(Line(label, rule)))));

	let proof = all(Many(some(line, comment)), 
		PopStack(arr => PushStack(Proof(arr.filter(v => v != null)))));

	return proof(nxt);
}

let to_parser = (grammar) => (str) => {
	let parse = grammar(all(wspace, Eq(null))(Id))(State(str, [], 0, 0, false));

	if(parse.fail){
		let lines = str.split("\n");
		let col = parse.index - lines.slice(0, parse.new_lines).join("\n").length + 1; 
		console.log(col);

		throw new Error("parse failed at line " + parse.new_lines + ":\n```\n" 
			+ lines.slice(Math.max(parse.new_lines - 1, 0), parse.new_lines + 1).join("\n") 
			+ "\n"
			+ "^".padStart(col, "~") 
			+ "\n"
			+ lines.slice(parse.new_lines + 1, parse.new_lines + 3).join("\n")
		+ "\n```");
	}

	return parse.stack[0];
}

let parse_prop = to_parser(prop_grammar);
let parse_proof = to_parser(proof_grammar);


