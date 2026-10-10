import Mathlib
import Submission.Work.MotT.kPointAux
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **Normalised Klein basis at the point at infinity.**

Let `D` be Klein data over a field `K`, `E = D.E.baseChange K`, `x = genX E`, `w = infW E = y/x²`, and
put `g = ⟨x·w², …⟩ ∈ ↥(infPlace E)`.  The hypothesis `hg` says that `g - 1` lies in the maximal
ideal `𝔪` of the local ring at infinity, i.e. that the unit `g = x·w²` of the discrete valuation ring
`↥(infPlace E)` reduces to `1` modulo `𝔪` (this is `Work.MotT.infW_genX_sub_one_mem`).

Then there is a normalised form `N : Fin 5 → ↥(infPlace E)` of the Klein basis
`kleinBas D K = (1, x, y, x², x·y)` — namely `N = ![1, g, g², g², g³]` — such that

* `N m` is the element `w ^ (kP m) · kleinBas D K m` of `↥(infPlace E)` for each `m`, where
  `kP = ![0,2,3,4,5]` is the vector of pole orders at `O` (so `N` is obtained from the basis by
  multiplying by the uniformizer powers that make all five elements regular at `O`), and
* every `N m` is congruent to `1` modulo `𝔪`.

Route: take `g := ⟨genX E * (infW E)^2, genX_mul_infW_sq_mem_infPlace E⟩` and
`N := ![1, g, g^2, g^2, g^3]`.  For the first component use `fin_cases m` and `Subtype.ext`
(`Work.MotV.kleinBas D K m` unfolds definitionally to
`![1, genX E, genY E, (genX E)^2, genX E * genY E]`); the non-trivial cases are exactly the
identities `Work.MotT.infW_cube_mul_genY_eq`, `Work.MotT.infW_pow_four_mul_genX_sq_eq` and
`Work.MotT.infW_pow_five_mul_genX_mul_genY_eq` of `Submission/Work/MotT/kPointAux.lean` (rewriting
`(g : Func E) = genX E * (infW E)^2`).  For the second component, `N m` is `1` or `g^k`, and
`g^k - 1 = g·(g^{k-1} - 1) + (g - 1) ∈ 𝔪` by induction on `k` from `hg` (the case `k = 0` is
`1 - 1 = 0`). -/
theorem exists_norm_basis {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hg : ((⟨Work.MotC2.genX (D.E.baseChange K) * (Work.MotC2.infW (D.E.baseChange K)) ^ 2,
        Work.MotC2.genX_mul_infW_sq_mem_infPlace (D.E.baseChange K)⟩ :
          ↥(Work.MotC2.infPlace (D.E.baseChange K))) - 1) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K))) :
    ∃ N : Fin 5 → ↥(Work.MotC2.infPlace (D.E.baseChange K)),
      (∀ m : Fin 5, (N m : Work.MotC2.Func (D.E.baseChange K)) =
        (Work.MotC2.infW (D.E.baseChange K)) ^ (Work.MotT.kP m) * Work.MotV.kleinBas D K m) ∧
      (∀ m : Fin 5, N m - 1 ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K))) := by
  -- `g = x·w²` as an element of the local ring at infinity, i.e. the uniformizer power
  -- normalising the basis element `x` (the case `m = 1` of the first component below).
  let g : ↥(Work.MotC2.infPlace (D.E.baseChange K)) :=
    ⟨Work.MotC2.genX (D.E.baseChange K) * (Work.MotC2.infW (D.E.baseChange K)) ^ 2,
      Work.MotC2.genX_mul_infW_sq_mem_infPlace (D.E.baseChange K)⟩
  -- the hypothesis is exactly `g - 1 ∈ 𝔪`
  have hgmem : g - 1 ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)) := hg
  -- `g` is `x·w²` in the function field (`w = y/x²`)
  have hgval : ((g : ↥(Work.MotC2.infPlace (D.E.baseChange K))) : Work.MotC2.Func (D.E.baseChange K))
      = Work.MotC2.genX (D.E.baseChange K) * (Work.MotC2.infW (D.E.baseChange K)) ^ 2 := rfl
  -- every power of `g` is congruent to `1` modulo the maximal ideal:
  -- `g^{k+1} - 1 = g·(g^k - 1) + (g - 1)`
  have hpow : ∀ k : ℕ,
      (g ^ k - 1) ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h : g ^ (k + 1) - 1 = g * (g ^ k - 1) + (g - 1) := by ring
      rw [h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) hgmem
  refine ⟨![1, g, g ^ 2, g ^ 2, g ^ 3], ?_, ?_⟩
  · -- `w^{kP m}·b_m = g^{kQ m}` for the basis `b = (1, x, y, x², xy)`
    intro m
    fin_cases m <;> simp [Work.MotV.kleinBas, Work.MotT.kP]
    · rw [hgval]; exact mul_comm _ _
    · rw [hgval]; exact (Work.MotT.infW_cube_mul_genY_eq (D.E.baseChange K)).symm
    · rw [hgval]; exact (Work.MotT.infW_pow_four_mul_genX_sq_eq (D.E.baseChange K)).symm
    · rw [hgval]; exact (Work.MotT.infW_pow_five_mul_genX_mul_genY_eq (D.E.baseChange K)).symm
  · -- `g^{kQ m} ≡ 1` modulo the maximal ideal
    intro m
    fin_cases m
    · simp
    · exact hgmem
    · exact hpow 2
    · exact hpow 2
    · exact hpow 3

end Work.MotT
