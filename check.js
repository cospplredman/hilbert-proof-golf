let ND = {
	ref: 0,
	arrow: 1,
	not: 2,
	derived: 3,
};

let Ref = (name) => ({type: ND.ref, name});
let Arrow = (left, right) => ({type: ND.arrow, left, right});
let Not = (prop) => ({type: ND.not, prop});



let term_eq = (t1, t2) => {
	if(t1 === t2)
		return true;
	if(t1.type != t2.type)
		return false;

	switch(t1.type){
		case ND.ref:
			return t1.name == t2.name;
		case ND.arrow:
			return term_eq(t1.left, t2.left) && term_eq(t1.right, t2.right);
		case ND.not:
			return term_eq(t1.prop, t2.prop);
	}

	throw new Error("term_eq got something that wasn't a proposition...");
}

let print_prop = (t) => {
	switch(t.type){
		case ND.ref:
			return t.name;
		case ND.arrow:
			return (t.left.type == ND.arrow ? "(" : "") 
				+ print_prop(t.left)
				+ (t.left.type == ND.arrow ? ")" : "") + " -> " + print_prop(t.right);
		case ND.not:
			return "!" + (t.prop.type == ND.arrow ? "(" : "") 
				+ print_prop(t.prop) + (t.prop.type == ND.arrow ? ")" : "");
		case ND.derived:
			return "|- " + print_prop(t.prop);
	}

	throw new Error("print_prop got something that wasn't a proposition...");
}


let Derived = (prop) => ({type: ND.derived, prop});

let a1 = (a, b) => Derived(Arrow(a, Arrow(b, a)));
let a2 = (a, b, c) => Derived(Arrow(Arrow(a, Arrow(b, c)), Arrow(Arrow(a, b), Arrow(a, c))));
let a3 = (a, b) => Derived(Arrow(Arrow(Not(a), Not(b)), Arrow(b, a)));
let mp = (a, b) => {
	let ap = a.prop, bp = b.prop;
	if(ap.type == ND.arrow && term_eq(ap.left, bp)){
		return Derived(ap.right);
	}

	return null;
}

