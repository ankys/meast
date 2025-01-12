
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

#include "01_introduction.typ"
#include "02_measure.typ"
#include "03_integral.typ"
#include "04_lebesgue.typ"
#include "05_fubini.typ"
#include "06_differential.typ"

#bibliography("99_ref.yml")
