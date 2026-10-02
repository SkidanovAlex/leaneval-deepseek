import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.Gen.LhCalc
import Submission.Work.Gen.cupChern_lhTerm_zeta2
import Submission.Work.Gen.cupChern_zero_lhMap
import Submission.Work.Gen.PsiDataDefs
import Submission.Work.LerayHirsch.LH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Gen

open Work.TangentClasses Work.Thom
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The index `1` of the level `m+2` Leray–Hirsch decomposition. -/
abbrev oneIdx (m : ℕ) : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2} := ⟨⟨1, by omega⟩, by omega⟩

/-- The index `0` of the level `m+2` Leray–Hirsch decomposition. -/
abbrev zeroIdx (m : ℕ) : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2} := ⟨⟨0, by omega⟩, by omega⟩

/-- The index `j + 2` at level `m + 2`, for a non-top index `j` at level `m`.  The hypothesis
`(j : ℕ) < m` is exactly what makes `j + 2` a valid index of the level `m + 2` decomposition. -/
def idxOf {m : ℕ} (j : {j : Fin (m + 2) // (j : ℕ) ≤ m}) (hj : (j : ℕ) < m) :
    {i : Fin (m + 2) // (i : ℕ) ≤ m + 2} := ⟨⟨(j : ℕ) + 2, by omega⟩, by omega⟩

/-- The coefficient of the `j + 2`-nd Leray–Hirsch summand of `ζ²ψ`, transported to its degree. -/
noncomputable def coeffOf {B : Type} [TopologicalSpace B] {m : ℕ}
    (ψf : (j : {j : Fin (m + 2) // (j : ℕ) ≤ m}) → Work.Thom.Coh ℤ (2 * (m - (j : ℕ))) B)
    (j : {j : Fin (m + 2) // (j : ℕ) ≤ m}) (hj : (j : ℕ) < m) :
    Work.Thom.Coh ℤ (2 * ((m + 2) - ((j : ℕ) + 2))) B :=
  Work.Thom.cohTransport (by omega : 2 * (m - (j : ℕ)) = 2 * ((m + 2) - ((j : ℕ) + 2))) (ψf j)

/-- **The aligned double `ζ`-shift of a non-top Leray–Hirsch summand.**  The companion of
`Work.Gen.cupChern_lhTerm_zeta2`, stated for the level-`m` summands of the `ζ²ψ`-analysis (where
`n = m + 1`, so that `(n-1)+1` and `n+1` reduce to `m+1` and `m+2` definitionally). -/
theorem cruxCupShiftNonTop {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 2))) ι)
    (j : {j : Fin (m + 2) // (j : ℕ) ≤ m}) (hj : (j : ℕ) < m)
    (y : Work.Thom.Coh ℤ (2 * (m - (j : ℕ))) B) :
    Work.Whitney.cupChern (m + 1) 1
        (Work.Whitney.cupChern m 1 (Work.LerayHirsch.lhTerm W m j y) (Work.LerayHirsch.zeta W))
        (Work.LerayHirsch.zeta W)
      = Work.LerayHirsch.lhTerm W (m + 2) (idxOf j hj)
          (Work.Thom.cohTransport
            (by omega : 2 * (m - (j : ℕ)) = 2 * ((m + 2) - ((j : ℕ) + 2))) y) := by
  rw [Work.Gen.cupChern_lhTerm_zeta W (i := (j : Fin (m + 2))) (hi := j.2)
      (j := ⟨(j : ℕ) + 1, by omega⟩) (hj := rfl) (x := y)]
  rw [Work.Gen.cupChern_lhTerm_zeta W (i := ⟨(j : ℕ) + 1, by omega⟩) (hi := by omega)
      (j := ⟨(j : ℕ) + 2, by omega⟩) (hj := rfl) (x := _)]
  rw [Work.Whitney.cohTransport_trans]
  rfl

/-- **The aligned top `ζ`-shift**: the companion of `Work.Gen.cupChern_lhTerm_zeta_top` at the
level-`m` summands of the `ζ²ψ`-analysis, where the outer multiplication by `ζ` is well typed
without a degree cast (`(m+1) = ((m+1)-1)+1` definitionally). -/
theorem cruxCupTop {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 2))) ι)
    (y : Work.Thom.Coh ℤ 0 B)
    (c : (i : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) → Work.Thom.Coh ℤ (2 * ((m + 2) - (i : ℕ))) B)
    (hc : Work.LerayHirsch.lhMap W (m + 2) c = Work.LerayHirsch.zetaPow W (m + 2)) :
    Work.Whitney.cupChern (m + 1) 1
        (Work.Whitney.cupChern m 1
          (Work.LerayHirsch.lhTerm W m (Work.Gen.topCoeffIdx (n := m + 1))
            (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree' (n := m + 1)) y))
          (Work.LerayHirsch.zeta W))
        (Work.LerayHirsch.zeta W)
      = Work.LerayHirsch.lhMap W (m + 2)
          (fun i => Work.Thom.cohTransport
            (by omega : 2 * (0 + ((m + 2) - (i : ℕ))) = 2 * ((m + 2) - (i : ℕ)))
            (Work.Whitney.cupChern 0 ((m + 2) - (i : ℕ)) y (c i))) := by
  have hX : Work.LerayHirsch.lhTerm W m (Work.Gen.topCoeffIdx (n := m + 1))
        (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree' (n := m + 1)) y)
      = Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
          (Work.Whitney.cupChern 0 m
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ 0)) y)
            (Work.LerayHirsch.zetaPow W m)) := by
    rw [Work.LerayHirsch.lhTerm_def, Work.Thom.cohTransport_CohMap,
      Work.Gen.cupChern_cast_left, Work.Whitney.cohTransport_trans]
    rfl
  have hC1 : Work.Whitney.cupChern m 1
        (Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
          (Work.Whitney.cupChern 0 m
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ 0)) y)
            (Work.LerayHirsch.zetaPow W m)))
        (Work.LerayHirsch.zeta W)
      = Work.Thom.cohTransport (by omega : 2 * (0 + (m + 1)) = 2 * (m + 1))
          (Work.Whitney.cupChern 0 (m + 1)
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ 0)) y)
            (Work.LerayHirsch.zetaPow W (m + 1))) := by
    rw [Work.Gen.cupChern_cast_left]
    rw [Work.Gen.cupChern_assoc]
    rw [← Work.LerayHirsch.zetaPow_succ W m]
    rw [Work.Whitney.cohTransport_trans]
  have hC2 : Work.Whitney.cupChern (m + 1) 1
        (Work.Thom.cohTransport (by omega : 2 * (0 + (m + 1)) = 2 * (m + 1))
          (Work.Whitney.cupChern 0 (m + 1)
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ 0)) y)
            (Work.LerayHirsch.zetaPow W (m + 1))))
        (Work.LerayHirsch.zeta W)
      = Work.Thom.cohTransport (by omega : 2 * (0 + (m + 2)) = 2 * (m + 2))
          (Work.Whitney.cupChern 0 (m + 2)
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ 0)) y)
            (Work.LerayHirsch.zetaPow W (m + 2))) := by
    rw [Work.Gen.cupChern_cast_left]
    rw [Work.Gen.cupChern_assoc]
    rw [← Work.LerayHirsch.zetaPow_succ W (m + 1)]
    rw [Work.Whitney.cohTransport_trans]
  rw [hX, hC1, hC2]
  rw [← hc]
  rw [Work.Gen.cupChern_zero_lhMap]
  rw [Work.Whitney.cohTransport_trans]
  rw [Work.Whitney.ChernRel.cohTransport_self]

end

open Work.TangentClasses Work.Thom in
/-- **The Leray–Hirsch coefficient comparison of the crux.**  With `W` of rank `n+1`, `ψ` the class
whose existence is `(A)` (`y = π^*(x) + ζψ` for `y = c_n(Q)`) and `(B)`
(`ζ ⌣ y = π^*(e)`), and `c` the Chern-root expansion of `ζ^{n+1}` (`hc`), the index-`1` coefficient
of `(★)` `ζ π^*(x) + ζ²ψ = π^*(e)` in `H^{2(n+1)}(P(W))` reads
`x + (ψ_{n-1} ⌣ c_1) = 0`, i.e. `x = -(ψ_top ⌣ c_1)` where `ψ_top` is the top (`ζ^{n-1}`)
Leray–Hirsch coefficient of `ψ`.  The proof: derive `(★)` from `hA`/`hB` (`cupChern_add_left`,
`cupChern_cast_left`, `cupChern_comm`), expand `ψ = lhMap W (n-1) ψf`, shift twice with
`Work.Gen.cupChern_lhTerm_zeta2` away from the top index and with
`Work.Gen.cupChern_lhTerm_zeta_top` at the top index, rewrite `ζ π^*(x)` and `π^*(e)` by
`Work.LerayHirsch.lhTerm_one_index`/`lhTerm_zero_index`, and compare the Leray–Hirsch coefficients
at index `1` using the injectivity of `lhMap W (n+1)`. -/
theorem cruxComparison {n : ℕ} (hn : 1 ≤ n)
    {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (hLH : Work.LerayHirsch.LerayHirsch W)
    (x : Work.Thom.Coh ℤ (2 * n) B) (e : Work.Thom.Coh ℤ (2 * (n + 1)) B)
    (ψ : Work.Thom.Coh ℤ (2 * (n - 1)) (Work.LerayHirsch.ProjSpace W))
    (y : Work.Thom.Coh ℤ (2 * n) (Work.LerayHirsch.ProjSpace W))
    (ψf : (j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1}) → Work.Thom.Coh ℤ (2 * ((n - 1) - (j : ℕ))) B)
    (hψ : Work.LerayHirsch.lhMap W (n - 1) ψf = ψ)
    (hA : y = (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * n))) x
        + Work.Thom.cohTransport (Work.Gen.psiDataDegree n hn)
            (Work.Whitney.cupChern 1 (n - 1) (Work.LerayHirsch.zeta W) ψ))
    (hB : Work.Whitney.cupChern n 1 y (Work.LerayHirsch.zeta W)
        = (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * (n + 1)))) e)
    (c : (i : {i : Fin (n + 1) // (i : ℕ) ≤ n + 1}) → Work.Thom.Coh ℤ (2 * ((n + 1) - (i : ℕ))) B)
    (hc : Work.LerayHirsch.lhMap W (n + 1) c = Work.LerayHirsch.zetaPow W (n + 1)) :
    x = Work.Thom.cohTransport (by omega : 2 * (0 + ((n + 1) - 1)) = 2 * n)
          (Work.Whitney.cupChern 0 ((n + 1) - 1)
            (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := n))
              (-(ψf Work.Gen.topCoeffIdx)))
            (c ⟨⟨1, by omega⟩, by omega⟩)) := by
  -- Write `n = m + 1` (the case `n = 0` contradicts `hn`): this makes `n - 1` and `(n+1) - 1`
  -- *reduce* to `m` and `m+1`, so that the level-`m+1` and level-`m+2` Leray–Hirsch index sets and
  -- degree expressions are definitionally the ones of `lhMap W n` and `lhMap W (n+1)`.
  -- The proof is a coefficient comparison in the Leray–Hirsch basis of `H^{2(n+1)}(P(W))`:
  --   * `hstar` is `(★) : ζ π^*(x) + ζ²ψ = π^*(e)`;
  --   * `hFx` identifies the `ζ π^*(x)` coefficient family with the solo family at index `1`, and
  --     `hRF` identifies `π^*(e)` with the solo family at index `0` (the `x`- and `e`-parts);
  --   * `hsum`/`hsplit`/`hnon`/`htop` decompose `ζ²ψ` into `lhMap W (n+1) (NFnt + NFt)`: the
  --     non-top summands `j < m` are the double `ζ`-shift `cruxCupShiftNonTop` at index `j + 2`,
  --     the top summand overflows and is expanded with the Chern-root relation (`cruxCupTop`);
  --   * `hfam`/`hone` compare the two families at index `1` (injectivity of `lhMap W (n+1)`),
  --     where the non-top family contributes `0` and the top one contributes the transported
  --     product `y0 ⌣ c_1`; this gives `x + (y0 ⌣ c_1) = 0`.
  rcases n with _ | m
  · omega
  -- ### (★) : `ζ π^*(x) + ζ²ψ = π^*(e)`
  have hstar : Work.Whitney.cupChern (m + 1) 1
        ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * (m + 1)))) x)
        (Work.LerayHirsch.zeta W)
      + Work.Whitney.cupChern (m + 1) 1
        (Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
          (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta W) ψ))
        (Work.LerayHirsch.zeta W)
      = (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * (m + 1 + 1)))) e := by
    rw [← hB, hA, Work.Whitney.ChernRel.cupChern_add_left]
    rfl
  -- ### commuting the inner `ζ` to the right
  have hcomm : Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
        (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta W) ψ)
      = Work.Whitney.cupChern m 1 ψ (Work.LerayHirsch.zeta W) := by
    rw [Work.Whitney.ChernRel.cupChern_comm]
    rw [Work.Whitney.cohTransport_trans]
    exact Work.Whitney.ChernRel.cohTransport_self _ _
  -- ### the index set of the non-top summands
  let S : Finset {j : Fin (m + 1 + 1) // (j : ℕ) ≤ m} :=
    Finset.univ.erase (Work.Gen.topCoeffIdx (n := m + 1))
  have hmem_lt : ∀ j : {j : Fin (m + 1 + 1) // (j : ℕ) ≤ m}, j ∈ S → (j : ℕ) < m := by
    intro j hjmem
    have hjne : j ≠ Work.Gen.topCoeffIdx (n := m + 1) := (Finset.mem_erase.mp hjmem).1
    rcases lt_or_eq_of_le j.2 with hlt | heq
    · exact hlt
    · exact absurd (Subtype.ext (Fin.ext heq)) hjne
  -- ### the families
  let NFnt : (i : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) → Work.Thom.Coh ℤ (2 * ((m + 2) - (i : ℕ))) B :=
    fun i => ∑ jj ∈ S.attach, Work.LerayHirsch.lhSoloFamily (Work.Gen.idxOf jj.1 (hmem_lt jj.1 jj.2))
      (Work.Gen.coeffOf ψf jj.1 (hmem_lt jj.1 jj.2)) i
  let y0 : Work.Thom.Coh ℤ 0 B :=
    Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := m + 1))
      (ψf (Work.Gen.topCoeffIdx (n := m + 1)))
  let NFt : (i : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) → Work.Thom.Coh ℤ (2 * ((m + 2) - (i : ℕ))) B :=
    fun i => Work.Thom.cohTransport (by omega : 2 * (0 + ((m + 2) - (i : ℕ))) = 2 * ((m + 2) - (i : ℕ)))
      (Work.Whitney.cupChern 0 ((m + 2) - (i : ℕ)) y0 (c i))
  -- ### the `x`-summand
  have hFx : Work.LerayHirsch.lhMap W (m + 2) (Work.LerayHirsch.lhSoloFamily (Work.Gen.oneIdx m) x)
      = Work.Whitney.cupChern (m + 1) 1
          ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * (m + 1)))) x)
          (Work.LerayHirsch.zeta W) := by
    rw [Work.LerayHirsch.lhMap_eq_single W (m + 2) (Work.Gen.oneIdx m) x]
    rw [show Work.LerayHirsch.lhTerm W (m + 2) (Work.Gen.oneIdx m)
          = Work.LerayHirsch.lhTerm W (m + 2) ⟨⟨1, by omega⟩, by omega⟩ from rfl]
    rw [lhTerm_one_index (k := m + 2) W (by omega) (by omega) x]
    rw [Work.Whitney.ChernRel.cohTransport_self]
    rfl
  -- ### the `π^*(e)` coefficient family
  have hRF : Work.LerayHirsch.lhMap W (m + 2) (Work.LerayHirsch.lhSoloFamily (Work.Gen.zeroIdx m) e)
      = (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * (m + 1 + 1)))) e := by
    rw [Work.LerayHirsch.lhMap_eq_single W (m + 2) (Work.Gen.zeroIdx m) e]
    rw [show Work.LerayHirsch.lhTerm W (m + 2) (Work.Gen.zeroIdx m)
          = Work.LerayHirsch.lhTerm W (m + 2) ⟨⟨0, by omega⟩, by omega⟩ from rfl]
    rw [Work.LerayHirsch.lhTerm_zero_index (by omega) W (m + 2) e]
    rw [Work.Whitney.ChernRel.cohTransport_self]
    rfl
  -- ### expanding and splitting the `ζ²ψ` sum
  have hsum : Work.Whitney.cupChern (m + 1) 1
        (Work.Whitney.cupChern m 1 ψ (Work.LerayHirsch.zeta W)) (Work.LerayHirsch.zeta W)
      = ∑ j : {j : Fin (m + 1 + 1) // (j : ℕ) ≤ m},
          Work.Whitney.cupChern (m + 1) 1
            (Work.Whitney.cupChern m 1 (Work.LerayHirsch.lhTerm W m j (ψf j))
              (Work.LerayHirsch.zeta W))
            (Work.LerayHirsch.zeta W) := by
    rw [← hψ, Work.LerayHirsch.lhMap_apply]
    rw [Work.Gen.cupChern_sum_left]
    rw [Work.Gen.cupChern_sum_left]
    rfl
  have hsplit : (∑ j ∈ S,
          Work.Whitney.cupChern (m + 1) 1
            (Work.Whitney.cupChern m 1 (Work.LerayHirsch.lhTerm W m j (ψf j))
              (Work.LerayHirsch.zeta W))
            (Work.LerayHirsch.zeta W))
        + Work.Whitney.cupChern (m + 1) 1
            (Work.Whitney.cupChern m 1
              (Work.LerayHirsch.lhTerm W m (Work.Gen.topCoeffIdx (n := m + 1))
                (ψf (Work.Gen.topCoeffIdx (n := m + 1)))) (Work.LerayHirsch.zeta W))
            (Work.LerayHirsch.zeta W)
      = ∑ j : {j : Fin (m + 1 + 1) // (j : ℕ) ≤ m},
          Work.Whitney.cupChern (m + 1) 1
            (Work.Whitney.cupChern m 1 (Work.LerayHirsch.lhTerm W m j (ψf j))
              (Work.LerayHirsch.zeta W))
            (Work.LerayHirsch.zeta W) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ (Work.Gen.topCoeffIdx (n := m + 1)))
  -- ### the per-index shift of the non-top summands
  have hnon : (∑ jj ∈ S.attach,
          Work.Whitney.cupChern (m + 1) 1
            (Work.Whitney.cupChern m 1 (Work.LerayHirsch.lhTerm W m jj.1 (ψf jj.1))
              (Work.LerayHirsch.zeta W))
            (Work.LerayHirsch.zeta W))
      = ∑ jj ∈ S.attach, Work.LerayHirsch.lhTerm W (m + 2)
          (Work.Gen.idxOf jj.1 (hmem_lt jj.1 jj.2)) (Work.Gen.coeffOf ψf jj.1 (hmem_lt jj.1 jj.2)) := by
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    exact Work.Gen.cruxCupShiftNonTop W jj.1 (hmem_lt jj.1 jj.2) (ψf jj.1)
  -- ### the non-top family
  have hNFnt : Work.LerayHirsch.lhMap W (m + 2) NFnt
      = ∑ jj ∈ S.attach, Work.LerayHirsch.lhTerm W (m + 2)
          (Work.Gen.idxOf jj.1 (hmem_lt jj.1 jj.2)) (Work.Gen.coeffOf ψf jj.1 (hmem_lt jj.1 jj.2)) := by
    rw [Work.Gen.lhMap_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [Work.LerayHirsch.lhMap_eq_single]
  -- ### the top summand
  have hy0 : Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree' (n := m + 1))
        (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := m + 1))
          (ψf (Work.Gen.topCoeffIdx (n := m + 1)))) = ψf (Work.Gen.topCoeffIdx (n := m + 1)) := by
    rw [Work.Whitney.cohTransport_trans]
    exact Work.Whitney.ChernRel.cohTransport_self _ _
  have htop : Work.Whitney.cupChern (m + 1) 1
        (Work.Whitney.cupChern m 1
          (Work.LerayHirsch.lhTerm W m (Work.Gen.topCoeffIdx (n := m + 1))
            (ψf (Work.Gen.topCoeffIdx (n := m + 1)))) (Work.LerayHirsch.zeta W))
        (Work.LerayHirsch.zeta W)
      = Work.LerayHirsch.lhMap W (m + 2) NFt := by
    rw [← hy0]
    exact Work.Gen.cruxCupTop W y0 c hc
  -- ### the `ζ²ψ` part, in `lhMap` form
  have hchain : Work.Whitney.cupChern (m + 1) 1
        (Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
          (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta W) ψ))
        (Work.LerayHirsch.zeta W)
      = Work.LerayHirsch.lhMap W (m + 2) NFnt + Work.LerayHirsch.lhMap W (m + 2) NFt := by
    rw [hcomm]
    rw [hsum, ← hsplit]
    rw [← Finset.sum_attach]
    rw [hnon, htop, ← hNFnt]
  have hψsum : Work.Whitney.cupChern (m + 1) 1
        (Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
          (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta W) ψ))
        (Work.LerayHirsch.zeta W)
      = Work.LerayHirsch.lhMap W (m + 2) (fun i => NFnt i + NFt i) := by
    rw [hchain]
    exact (Work.Gen.lhMap_add W (m + 2) NFnt NFt).symm
  -- ### assembling
  have hkey := hstar
  rw [← hFx, hψsum, ← hRF] at hkey
  rw [← Work.Gen.lhMap_add] at hkey
  have hfam := Work.LerayHirsch.lhMap_injective_of_LerayHirsch W hLH (m + 2) hkey
  have hone := congrFun hfam (Work.Gen.oneIdx m)
  have hNFnt_one : NFnt (Work.Gen.oneIdx m) = 0 := by
    rw [show NFnt (Work.Gen.oneIdx m)
        = ∑ jj ∈ S.attach, Work.LerayHirsch.lhSoloFamily (Work.Gen.idxOf jj.1 (hmem_lt jj.1 jj.2))
            (Work.Gen.coeffOf ψf jj.1 (hmem_lt jj.1 jj.2)) (Work.Gen.oneIdx m) from rfl]
    refine Finset.sum_eq_zero (fun jj _ => ?_)
    refine Work.LerayHirsch.lhSoloFamily_of_ne _ (fun hcontra => ?_)
    have hval := congrArg (fun t : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2} => (t : ℕ)) hcontra
    have h2 : ((Work.Gen.idxOf jj.1 (hmem_lt jj.1 jj.2) : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) : ℕ)
        = (jj.1 : ℕ) + 2 := rfl
    have h3 : ((Work.Gen.oneIdx m : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) : ℕ) = 1 := rfl
    omega
  have hne : (Work.Gen.oneIdx m : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) ≠ Work.Gen.zeroIdx m := by
    intro h
    have hval := congrArg (fun t : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2} => (t : ℕ)) h
    have h1 : ((Work.Gen.oneIdx m : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) : ℕ) = 1 := rfl
    have h0 : ((Work.Gen.zeroIdx m : {i : Fin (m + 2) // (i : ℕ) ≤ m + 2}) : ℕ) = 0 := rfl
    omega
  rw [Work.LerayHirsch.lhSoloFamily_self, hNFnt_one, zero_add,
    Work.LerayHirsch.lhSoloFamily_of_ne _ hne] at hone
  have hx : x = - NFt (Work.Gen.oneIdx m) := eq_neg_of_add_eq_zero_left hone
  -- ### identification with the goal
  have hgoal : Work.Thom.cohTransport (by omega : 2 * (0 + ((m + 1 + 1) - 1)) = 2 * (m + 1))
        (Work.Whitney.cupChern 0 ((m + 1 + 1) - 1)
          (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := m + 1))
            (-(ψf (Work.Gen.topCoeffIdx (n := m + 1)))))
          (c ⟨⟨1, by omega⟩, by omega⟩))
      = - NFt (Work.Gen.oneIdx m) := by
    rw [Work.Whitney.ChernRel.cohTransport_neg, Work.Whitney.ChernRel.cupChern_neg_left,
      Work.Whitney.ChernRel.cohTransport_neg]
  exact hx.trans hgoal.symm

end Work.Gen
