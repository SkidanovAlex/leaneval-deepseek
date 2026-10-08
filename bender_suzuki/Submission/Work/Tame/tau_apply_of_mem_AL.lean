import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_AU_iff
import Submission.Work.Tame.ft95_tau_apply_of_mem_AL

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- **Feit–Thompson Lemma 9.1, value part** (p. 805).  Let `L̂` be tamely imbedded in `X` with
system of supporting subgroups `Hs`, and let `α ∈ 𝓒₀(L̂)`.  If `j` is one of Feit–Thompson's indices
`0 ≤ j ≤ n` (`j : Idx n = Option (Fin n)`, with `none` for `j = 0`, i.e. `𝔎_0 = 1`) and
`L ∈ 𝔏_j = LofIdx Lhat n Hs j` — that is, `L ∈ 𝔏_0 = {L ∈ L̂ | C(L) ⊆ 𝔏}` for `j = 0` and
`L ∈ 𝔏_i = {L ∈ 𝔇 | C(L) ⊆ 𝔑_i}` for `j = some i` — then for
`A ∈ 𝔄_L = ALofIdx Lhat n Hs j L` (which is `{L}` for `j = 0` and `L{𝔎_i ∩ C(L)}` for
`j = some i`) one has `α^τ(A) = α(L)`.

The hypothesis `HasTameData Lhat n Hs` (`𝔇 ≠ ∅ ∨ n = 0`, see `Submission/Work/Tame/NOTES.md` §1)
is required because `projEC` is totalised by `Classical.choose`: when `𝔇 = ∅` and `n ≥ 1` the
supporting subgroups are unconstrained and the extra terms of (9.4) need not vanish at `L`; with
`n = 0` the sum in (9.4) is empty, and when `𝔇 ≠ ∅` Definition 9.1(ii)(c) pins `projEC` down.

Feit–Thompson's proof: `α^τ(A) = α^*(A) + (α_{i1} - α_{i2})^*(A)` for `i ≥ 1` (9.6); the
T. I. set property of `Ñ_i` and `N(Ñ_i) = 𝔑_i` turn `(α_{i1} - α_{i2})^*(A)` into
`(α_{i1} - α_{i2})(A)` (9.7); and (9.5) together with (9.3) (`|C(L)| = |C(L) ∩ 𝔏|·|𝔄_L|`) give the
value `α(L)`.  For `i = 0` one uses `C(L) ⊆ 𝔏`, so `α^*(L) = α(L)`, and every term of (9.4) with
`i ≥ 1` vanishes at `L`.

The argument is assembled in `Submission/Work/Tame/ft95_tau_apply_of_mem_AL.lean` from the
following pieces, each of which is proved in its own module of this area:

* `alphaI2LM_apply_eq_card` — for `N ∈ 𝔑_i` and `M = projEC N`, the induced function `α_{i2}`
  takes at `N` the value `#{k ∈ 𝔎_i | k⁻¹Nk = M} · α(M)` (this is the computation behind (9.5));
* `beta_eq_zero_of_notMem_hatNp` — `α_{i1} - α_{i2}` vanishes on `𝔑_i − Ñ_i^#` when the
  centralizer of the point in `𝔎_i` is trivial (the T. I. input, (9.7));
* `indFun_Lgrp_apply_of_mem_Lhat` — for `L ∈ L̂^#`, `Ind_𝔏^X α (L)·|C_𝔏(L)| = α(L)·|C_X(L)|`
  (the count of `L̂`-elements in the `𝔏`-class of `L`, using (i));
* `card_centralizer_eq_mul_of_mem_Lset` — (9.3), `|C(L)| = |C_𝔏(L)|·|C_{𝔎_i}(L)|` for `L ∈ 𝔏_i`;
* `conj_mul_notMem_Lhat`, `not_isConj_hatNp_of_mem_L0set`, `not_isConj_hatNp_of_mem_Lset` —
  the order/coprimality and fusion arguments showing that a conjugate of `L` (or of
  `A = LH ∈ 𝔄_L` with `H ≠ 1`) never lands in the relevant T. I. set, respectively in `L̂^#`;
* `indFun_hatNp_apply` — the T. I. set form of the induction formula on `Ñ_i^#`.

This module is the canonical path for the value part; the identical statement is proved in
`ft95_tau_apply_of_mem_AL` (an independent assembly of the same pieces), which is what is used
below. -/
theorem tau_apply_of_mem_AL {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {j : Idx n} {L : ↥(Lgrp Lhat)}
    (hL : (L : X) ∈ LofIdx Lhat n Hs j)
    {A : X} (hA : A ∈ ALofIdx Lhat n Hs j (L : X)) :
    tau Lhat n Hs α A = α L :=
  ft95_tau_apply_of_mem_AL h hD hα hL hA

end Work.Tame
