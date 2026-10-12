import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.Split

open MeasureTheory

/-- `EuclideanSpace ℝ (Fin 3)`, the one-particle configuration space. -/
abbrev Euc3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `n`-particle configuration space. -/
abbrev Xfin (n : ℕ) : Type := Submission.BoseGases.X n

/-- The hypothesis-side integrand `(u,q) ↦ χ_ℓ(u)·W(q)·χ_ℓ(u−q)`. -/
noncomputable def Gfun (ℓ : ℝ) (g : Euc3 → ℝ) (q : Euc3 × Euc3) : ℝ :=
  Submission.BoseGases.chiScale ℓ q.1 * Submission.BoseGases.wScaled ℓ g q.2
    * Submission.BoseGases.chiScale ℓ (q.1 - q.2)

/-- The conclusion-side integrand `(y,z) ↦ χ_ℓ(y)·W(y−z)·χ_ℓ(z)`. -/
noncomputable def Hfun (ℓ : ℝ) (g : Euc3 → ℝ) (q : Euc3 × Euc3) : ℝ :=
  Submission.BoseGases.chiScale ℓ q.1 * Submission.BoseGases.wScaled ℓ g (q.1 - q.2)
    * Submission.BoseGases.chiScale ℓ q.2

/-- The shear `(y,z) ↦ (y, y−z)` of `ℝ³ × ℝ³` is measure preserving for the Lebesgue
product measure: it is the composite of the negation in the second slot
(`MeasurePreserving.prod` with `Measure.measurePreserving_neg`) with the shear
`(y,w) ↦ (y, y+w)` of `measurePreserving_prod_add`. -/
lemma shear_measurePreserving :
    MeasurePreserving (fun p : Euc3 × Euc3 => (p.1, p.1 - p.2))
      ((volume : Measure Euc3).prod volume) ((volume : Measure Euc3).prod volume) :=
  (measurePreserving_prod_add (volume : Measure Euc3) (volume : Measure Euc3)).comp
    ((MeasurePreserving.id (volume : Measure Euc3)).prod
      (Measure.measurePreserving_neg (volume : Measure Euc3)))

/-- Substituting the shear turns the hypothesis integrand into the conclusion integrand,
so integrability transfers. -/
lemma integrable_Hfun {ℓ : ℝ} {g : Euc3 → ℝ}
    (hprod : Integrable (Gfun ℓ g) ((volume : Measure Euc3).prod volume)) :
    Integrable (Hfun ℓ g) ((volume : Measure Euc3).prod volume) := by
  have hGσ : Integrable (fun q : Euc3 × Euc3 => Gfun ℓ g (q.1, q.1 - q.2))
      ((volume : Measure Euc3).prod volume) :=
    shear_measurePreserving.integrable_comp_of_integrable hprod
  refine hGσ.congr ?_
  filter_upwards with q
  simp only [Gfun, Hfun]
  rw [sub_sub_cancel]

/-! Route: the two-slot peel of `abox n ℓ` plus the shear `(u,q) ↦ (u, u-q)` of `ℝ³ × ℝ³`
(a linear measure-preserving bijection, unit Jacobian), which turns the hypothesis's integrand
`chiScale ℓ u * wScaled ℓ g q * chiScale ℓ (u-q)` into the conclusion's
`chiScale ℓ u * wScaled ℓ g (u-v) * chiScale ℓ v`.  Peeling slot `i` (`Q0Sector.abox_peel_mp`,
the measure-preserving `kcInsN`), then slot `j` of the remaining `(n-1)` coordinates, writes the box
integral as `ℓ^(3*(n-2))` times the integral over `acube ℓ × acube ℓ`, and that double integral over
the cube is dominated by the given product integral over `ℝ³ × ℝ³` (`Integrable.integrableOn`,
`IntegrableOn.mono_set`, nonnegative absolute values). -/
theorem integrableOn_abox_of_prod {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hprod : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ q.1 * Submission.BoseGases.wScaled ℓ g q.2
          * Submission.BoseGases.chiScale ℓ (q.1 - q.2))
      (MeasureTheory.volume.prod MeasureTheory.volume))
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.chiScale ℓ (x i) * Submission.BoseGases.wScaled ℓ g (x i - x j)
          * Submission.BoseGases.chiScale ℓ (x j))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  by_cases hn : 2 ≤ n
  · -- write `n = p + 2` and peel the two slots `i` and `j = i.succAbove j'`
    obtain ⟨p, hp⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    subst n
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
    -- the measures: the centred cube, the boxes on the remaining coordinates, the box
    let μA : Measure Euc3 := (volume : Measure Euc3).restrict (Submission.BoseGases.acube ℓ)
    let ν1 : Measure (Xfin (p + 1)) :=
      (volume : Measure (Xfin (p + 1))).restrict (Submission.BoseGases.abox (p + 1) ℓ)
    let ν2 : Measure (Xfin p) :=
      (volume : Measure (Xfin p)).restrict (Submission.BoseGases.abox p ℓ)
    let κ : Measure (Xfin (p + 2)) :=
      (volume : Measure (Xfin (p + 2))).restrict (Submission.BoseGases.abox (p + 2) ℓ)
    let ρ : Measure (Euc3 × (Euc3 × Xfin p)) := μA.prod (μA.prod ν2)
    -- the two-slot reinsertion equivalence
    let E : Euc3 × (Euc3 × Xfin p) ≃ᵐ Xfin (p + 2) :=
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Euc3) (Submission.BoseGases.kcInsN p j')).trans
        (Submission.BoseGases.kcInsN (p + 1) i)
    -- the conclusion integrand is integrable on the full product space
    have hH : Integrable (Hfun ℓ g) ((volume : Measure Euc3).prod volume) :=
      integrable_Hfun hprod
    -- peel step 1: slot `i`
    have h1 : MeasurePreserving (⇑(Submission.BoseGases.kcInsN (p + 1) i)) (μA.prod ν1) κ := by
      have h := MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 2) => Euc3) i)
        (Submission.BoseGases.abox_peel_mp (n := p + 1) ℓ i)
      simpa [μA, ν1, κ, Submission.BoseGases.kcInsN] using h
    -- peel step 2: slot `j'` among the remaining coordinates
    have h2 : MeasurePreserving (⇑(Submission.BoseGases.kcInsN p j')) (μA.prod ν2) ν1 := by
      have h := MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => Euc3) j')
        (Submission.BoseGases.abox_peel_mp (n := p) ℓ j')
      simpa [μA, ν2, ν1, Submission.BoseGases.kcInsN] using h
    have h2'' : MeasurePreserving
        (⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.refl Euc3) (Submission.BoseGases.kcInsN p j')))
        (μA.prod (μA.prod ν2)) (μA.prod ν1) := by
      have hh := (MeasurePreserving.id μA).prod h2
      exact hh
    have hE : MeasurePreserving (⇑E) ρ κ := by
      have hh := h1.comp h2''
      simpa [E, ρ, MeasurableEquiv.coe_trans] using hh
    -- the pushforward of `ρ` under the first-coordinates projection
    have hmapψ : Measure.map (Prod.map id Prod.fst : Euc3 × (Euc3 × Xfin p) → Euc3 × Euc3) ρ
        = (ν2 Set.univ) • (μA.prod μA) := by
      have h1' := Measure.map_prod_map (μa := μA) (μc := μA.prod ν2)
        (f := id) (g := Prod.fst) measurable_id measurable_fst
      rw [Measure.map_id] at h1'
      rw [Measure.map_fst_prod] at h1'
      rw [Measure.prod_smul_right] at h1'
      exact h1'.symm
    have hν2univ : ν2 Set.univ = (volume : Measure (Xfin p)) (Submission.BoseGases.abox p ℓ) := by
      change ((volume : Measure (Xfin p)).restrict (Submission.BoseGases.abox p ℓ)) Set.univ = _
      rw [Measure.restrict_apply_univ]
    have hν2top : ν2 Set.univ ≠ ⊤ := by
      rw [hν2univ, Submission.BoseGases.abox_volume p ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top
    have hle : (ν2 Set.univ) • (μA.prod μA) ≤ (ν2 Set.univ) • ((volume : Measure Euc3).prod volume) :=
      smul_le_smul_left (ν2 Set.univ)
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
    have hHsm : Integrable (Hfun ℓ g) ((ν2 Set.univ) • (μA.prod μA)) :=
      Integrable.of_measure_le_smul hν2top hle hH
    have hψmp : MeasurePreserving (Prod.map id Prod.fst : Euc3 × (Euc3 × Xfin p) → Euc3 × Euc3) ρ
        ((ν2 Set.univ) • (μA.prod μA)) :=
      MeasurePreserving.mk (by fun_prop) hmapψ
    -- the integrand on the peeled space, independent of the trailing coordinates
    have key : Integrable (fun q : Euc3 × (Euc3 × Xfin p) => Hfun ℓ g (q.1, q.2.1)) ρ :=
      hψmp.integrable_comp_of_integrable hHsm
    have hEapp : ∀ q : Euc3 × (Euc3 × Xfin p),
        ⇑E q = Submission.BoseGases.kcInsN (p + 1) i (q.1, Submission.BoseGases.kcInsN p j' q.2) := by
      intro q
      rw [MeasurableEquiv.trans_apply]
      rfl
    -- pointwise identification of the conclusion integrand with `Hfun` after reinsertion
    have hpt : ∀ q : Euc3 × (Euc3 × Xfin p),
        (fun x : Xfin (p + 2) => Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.wScaled ℓ g (x i - x j) * Submission.BoseGases.chiScale ℓ (x j))
          (E q) = Hfun ℓ g (q.1, q.2.1) := by
      intro q
      have hEi : E q i = q.1 := by
        rw [hEapp]
        exact Submission.BoseGases.kc_insN_apply_same (p + 1) i q.1 (Submission.BoseGases.kcInsN p j' q.2)
      have hEj : E q j = q.2.1 := by
        rw [← hj', hEapp, Submission.BoseGases.kc_insN_apply_succ]
        exact Submission.BoseGases.kc_insN_apply_same p j' q.2.1 q.2.2
      simp only [hEi, hEj, Hfun]
    -- assemble: transport along `E` and identify with `key`
    rw [show MeasureTheory.IntegrableOn _ _ _ = Integrable (fun x : Xfin (p + 2) =>
        Submission.BoseGases.chiScale ℓ (x i) * Submission.BoseGases.wScaled ℓ g (x i - x j)
          * Submission.BoseGases.chiScale ℓ (x j)) κ from rfl]
    have hiff : Integrable (fun x : Xfin (p + 2) => Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.wScaled ℓ g (x i - x j) * Submission.BoseGases.chiScale ℓ (x j)) κ ↔
        Integrable ((fun x : Xfin (p + 2) => Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.wScaled ℓ g (x i - x j) * Submission.BoseGases.chiScale ℓ (x j))
          ∘ ⇑E) ρ := by
      have h := integrable_map_equiv (μ := ρ) E (fun x : Xfin (p + 2) =>
        Submission.BoseGases.chiScale ℓ (x i) * Submission.BoseGases.wScaled ℓ g (x i - x j)
          * Submission.BoseGases.chiScale ℓ (x j))
      rwa [hE.map_eq] at h
    rw [hiff]
    exact key.congr (Filter.Eventually.of_forall (fun q => (hpt q).symm))
  · -- fewer than two particles: there is no pair of distinct slots
    exfalso
    have hn1 : n ≤ 1 := by omega
    have hsub : Subsingleton (Fin n) :=
      ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
    exact hij (@Subsingleton.elim (Fin n) hsub i j)

end Work.BoseFixB3.Split
