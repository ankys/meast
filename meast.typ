
#let title = [測度と積分]
#let author = [中安淳]
#let date = datetime.today().display()
// #let date = [2025年1月4日]

#import "deps/jbook.typ": jbook, maketitle
#show: jbook.with()

#import "deps/autoeqnum.typ": autoeqnum
#show heading.where(level: 2): it => {
	counter(math.equation).update(0)
	it
}
#show: autoeqnum.with(mode: "ref", numbering: it => {
	let count = counter(heading).get()
	numbering("(1.1)", ..count, it)
})

#maketitle(
	title: title,
	author: author,
	date: date,
)

#include "00_preface.typ"

#outline()

// #include "01_tuple.typ"
// #include "02_space.typ"
// #include "03_pdiff.typ"
// #include "04_iint.typ"
// #include "05_fseq.typ"
// #include "06_calc.typ"
// #include "07_limint.typ"

// #bibliography("99_ref.yml")
