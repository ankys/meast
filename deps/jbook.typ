
#import "@preview/hydra:0.5.1": hydra
#let jbook(doc) = {
	let page-header = context{
		let page-num = here().page()
		if calc.odd(page-num) [
			#hydra(2)#h(1fr)*#page-num*
		] else [
			*#page-num*#h(1fr)#hydra(1)
		]
	}
	set page(paper: "a4", margin: (left: 15mm, right: 15mm, top: 30mm, bottom: 20mm), numbering: "1")
	set text(size: 10pt)

	set text(lang: "ja")

	let mincho = ("Libertinus Serif", "Noto Serif CJK JP", "YuMincho")
	let gothic = ("Libertinus Serif", "Noto Sans CJK JP", "YuGothic")
	set text(font: mincho)
	show emph: set text(font: gothic, weight: "bold")
	show strong: set text(font: gothic, weight: "bold")

	set page(header: page-header, footer: none)
	set heading(numbering: "第1章")
	show heading.where(level: 2): set heading(numbering: "1.1")

	show heading.where(level: 1): it => {
		pagebreak(weak: true, to: "odd")
		v(5em)
		if (it.numbering != none) {
			let number = numbering(it.numbering, counter(heading).get().first())
			block(text(1.5em)[*#number*])
		}
		v(3em, weak: true)
		block(text(2em)[*#it.body*])
		v(5em, weak: true)
	}
	show heading.where(level: 2): it => {
		strong(it)
		// par(text(size: 0pt, ""))
	}

	show outline: set heading(numbering: none)
	show outline.entry.where(level: 1): strong
	// show outline.entry.where(level: 1): set outline.entry(fill: none)

	set par(first-line-indent: 1em)
	// set par(hanging-indent: -1em)

	show math.equation.where(block: true): block.with(width: 100%)

	doc
}

#let maketitle(title: none, author: none, date: none) = {
	pagebreak(weak: true)
	align(center + horizon)[
		#text(2em)[*#title*]
		#v(3em, weak: true)
		#author
		#v(2em, weak: true)
		#date
	]
	set page(header: none)
	pagebreak()
	set page(header: none)
}
