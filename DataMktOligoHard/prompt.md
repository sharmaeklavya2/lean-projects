I have written a paper on oligopolistic data markets. It was accepted to ICML 2026 (as a spotlight paper). One of the theoretical results has a 13-page-long proof. _Finding_ the proof required a deep understanding of the problem, but _understanding_ the proof mostly just requires very long and laborious calculations. The proof's length is a deterrent to establishing the result's credibility, so I think a formalization in Lean would be very helpful, both for us authors and the community at large.

## Understanding the Result

Reading the original paper might not be the best use of your context window (the paper includes other results, discussion of prior work, etc), so I have prepared a new version for you with just the relevant details. In `DataMktOligoHard/paper/`, read `intro.tex`, then `revenue.tex`, and then `inapprox.tex`. `inapprox.tex` states the main result(s) that I want to formalize. (`revenue.tex` has some results too, but I don't want to formalize those. So we will take those as given.)

The lean file `DataMktOligoHard/Basic.lean` contains the necessary definitions. `DataMktOligoHard/Pending.lean` contains the main result (and maybe some other results too), with `sorry` for proof. We are yet to prove these.

## Proof of the Result

The proof of the main result is split across 5 TeX files in `DataMktOligoHard/paper`: `sp-props.tex`, `case1.tex`, `case2.tex`, `case3.tex`, `case4.tex`. Unlike the files in `part1`, the files in `part2` are copied mostly verbatim from the original paper, so you may observe a few minor notational inconsistencies.

The file `inapprox.tex` defines 4 points: $(p_i, q_i)$ for $i ∈ [4]$. `sp-props.tex` proves several properties of these points. The proof of the main theorem (`thm:pq` in tex, `cStar_le_μ` in lean) is split into 4 cases, each in its own tex file. These case files use some results from `sp-props.tex`.

When proving stuff in lean, I would like to have one lean file for each of the 5 tex files. In `DataMktOligoHard/`, `SpecialPoints.lean` formalizes `sp-props.tex`. `Case1.lean` would formalize `case1.tex`, and so on. Additionally, `Basic.lean` just has definitions that the other files would need, and we can rename `Pending.lean` to something else (`Main.lean` maybe?) later.

## How to Work

I want you editing in a tight write-and-compile loop. You should formalize at most one lemma from the paper before reporting back to me (unless I specifically say so otherwise). Even for a single lemma in the paper, if you ever feel that it's appropriate to break it into multiple lean theorems, please do so. Even within a single lean theorem, if you think it would help to formalize a little bit, `sorry` the rest, check if it compiles, and repeat, feel free to do so.

If you split a paper's lemma into multiple lean theorems, I would like you to have a "paper-facing lean theorem" that's basically a logical-and of the intermediate lean theorems. This helps me verify that the paper's lemma has been fully formalized. You will find examples of such paper-facing theorems in `SpecialPoints.lean`.

If you feel stuck, need clarifications, or want to discuss something at any point, do not hesitate to talk to me.

I'm a beginner at lean. I'm counting on your expertise at lean.

## What to do Now

First, from `paper/`, read `intro.tex`, then `revenue.tex`, then `inapprox.tex`. This will explain _what_ we are trying to prove. Then read `Basic.lean` and `Pending.lean`. Stop and ask any questions if you have them.

Then read `paper/sp-props.tex` and `SpecialPoints.lean`.
Then ask me about the current status of the project, and I will tell you want to do next.
