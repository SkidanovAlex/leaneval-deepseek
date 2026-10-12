import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace Work.BoseDict

/-! ## The support of a single-mode creation

`cre m l` is `Finsupp.mapDomain` along the injection `α ↦ α + e m l` of the multi-index
monoid, hence its support is the image of `q.support` and every element of the support
is `γ + e m l` with `γ ∈ q.support`. -/

/-- The shift `α ↦ α + e m l` of multi-indices, as an embedding (it is injective because
`(α + e m l) - e m l = α` in the canonically ordered monoid `Fin m →₀ ℕ`). -/
private noncomputable def addShiftEmb (m : ℕ) (l : Fin m) : (Fin m →₀ ℕ) ↪ (Fin m →₀ ℕ) :=
  ⟨fun α => α + Work.BoseB4.e m l, by
    intro a b h
    have h' := congrArg (fun f : Fin m →₀ ℕ => f - Work.BoseB4.e m l) h
    ext x
    have hx := congrArg (fun f : Fin m →₀ ℕ => f x) h'
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Work.BoseB4.e, Finsupp.single_apply] at hx
    by_cases hxl : l = x
    · rw [if_pos hxl] at hx; omega
    · rw [if_neg hxl] at hx; omega⟩

/-- `cre m l` is `Finsupp.mapDomain` along the shift `α ↦ α + e m l`. -/
private lemma cre_eq_mapDomain {m : ℕ} (l : Fin m) (q : Work.BoseB4.RealFock m) :
    Work.BoseB4.cre m l q
      = Finsupp.mapDomain (fun α : Fin m →₀ ℕ => α + Work.BoseB4.e m l) q := by
  ext β
  rw [Work.BoseB4.cre, Finsupp.lsum_apply, Finsupp.mapDomain,
    Finsupp.sum_apply, Finsupp.sum_apply]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [Finsupp.lsingle_apply]

/-- `cre m l` is `Finsupp.embDomain` along the shift embedding. -/
private lemma cre_eq_embDomain {m : ℕ} (l : Fin m) (q : Work.BoseB4.RealFock m) :
    Work.BoseB4.cre m l q = Finsupp.embDomain (addShiftEmb m l) q := by
  rw [cre_eq_mapDomain, Finsupp.embDomain_eq_mapDomain]
  rfl

/-- The support of a single-mode creation is the image of the support under the shift. -/
private lemma support_cre {m : ℕ} (l : Fin m) (q : Work.BoseB4.RealFock m) :
    (Work.BoseB4.cre m l q).support = q.support.map (addShiftEmb m l) := by
  rw [cre_eq_embDomain, Finsupp.support_embDomain]

/-- The degree of the unit multi-index `e m l` is one. -/
private lemma e_sum {m : ℕ} (l : Fin m) :
    (Work.BoseB4.e m l).sum (fun _ k => k) = 1 := by
  rw [Work.BoseB4.e]
  exact Finsupp.sum_single_index rfl

/-- **A superposed creation raises the degree by one** — the creation twin of
`Work.BoseDict.annOf_support_degree`: if every monomial of `Ψ` has degree `n`, then every monomial
of `creOf m w Ψ` has degree `n + 1`.

(`creOf m w = Σ_l w l • cre m l` and `cre m l` is the `Finsupp.lsum` sending `single α c` to
`single (α + e m l) c`, so the support of `creOf m w Ψ` is contained in the union over `l` of the
images of `Ψ.support` under `α ↦ α + e m l`; the degree then raises by one via
`Finsupp.sum_add_index` plus `e_degree`.  Needed by
`Work.BoseDict.boxRealise_creOf_annOf_creOf_annOf`, whose intermediate vector
`creOf w₂ (annOf v₂ Ψ)` is fed to `Work.BoseDict.boxRealise_annOf` and hence needs its degree.
There is no truncated-subtraction corner here, unlike the `annOf` twin: membership in the support
forces `β l ≥ 1`.) -/
theorem creOf_support_degree {m n : ℕ} (w : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = n) :
    ∀ β ∈ (Work.BoseB4.creOf m w Ψ).support, β.sum (fun _ k => k) = n + 1 := by
  intro β hβ
  rw [Finsupp.mem_support_iff] at hβ
  -- `creOf m w Ψ = Σ_l w l • cre m l Ψ`, so its value at `β` is the same combination.
  have h : (Work.BoseB4.creOf m w) Ψ
      = ∑ l : Fin m, (w l) • (Work.BoseB4.cre m l Ψ) := by
    rw [Work.BoseB4.creOf, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun l _ => LinearMap.smul_apply (w l) (Work.BoseB4.cre m l) Ψ
  have hsum : (Work.BoseB4.creOf m w Ψ) β
      = ∑ l : Fin m, w l * (Work.BoseB4.cre m l Ψ) β := by
    rw [h, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Finsupp.smul_apply, smul_eq_mul]
  rw [hsum] at hβ
  -- Some mode contributes, hence `(cre m l Ψ) β ≠ 0`.
  obtain ⟨l, hl⟩ : ∃ l : Fin m, w l * (Work.BoseB4.cre m l Ψ) β ≠ 0 := by
    by_contra hc
    rw [not_exists] at hc
    exact hβ (Finset.sum_eq_zero fun l _ => by
      by_contra h0
      exact hc l h0)
  have hcl : (Work.BoseB4.cre m l Ψ) β ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
  have hmem : β ∈ (Work.BoseB4.cre m l Ψ).support := Finsupp.mem_support_iff.mpr hcl
  -- So `β = γ + e m l` for some `γ` in the support of `Ψ`, and degrees add.
  rw [support_cre] at hmem
  obtain ⟨γ, hγ, hγβ⟩ := Finset.mem_map.mp hmem
  have hβeq : β = γ + Work.BoseB4.e m l := hγβ.symm
  rw [hβeq, Finsupp.sum_add_index' (fun a => rfl) (fun a b₁ b₂ => rfl), hΨ γ hγ, e_sum l]

end Work.BoseDict
