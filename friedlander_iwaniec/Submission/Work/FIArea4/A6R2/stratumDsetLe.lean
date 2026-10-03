import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.A6R2.EvGSupport
import Submission.Work.FIArea4.S15red.EvarG_filtered_strU_defs
import Submission.Work.S15crux.prelude

namespace Work.FIArea4.A6R2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Coprimality of the quadrant array of the stratum `U`.**  If the quadrant array
`quadArrE (KK Pa) (S15strU β u t ℓ e) σ₁ σ₂` does not vanish at `(r,s)`, then `β` does not vanish
at the point `scalePt e ⟨σ₁ r, σ₂ s⟩`, so FI (11.6) `(Re, 2 Im) = 1` gives
`Nat.Coprime (e·|σ₁|·r) (2·|σ₂|·s)`; since `r ∣ e·|σ₁|·r` and `2 s ∣ 2·|σ₂|·s`, the coprimality
descends to `Nat.Coprime r (2 * s)`.  This is the hypothesis FI (11.6) of the Proposition-14.1
bracket, in the form needed by `hCp`. -/
lemma quadArrE_strU_coprime (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ)
    (σ₁ σ₂ : ℤ) :
    ∀ r s : ℕ, Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
        (Work.FIArea4.S15strU β u t ℓ e) σ₁ σ₂ r s ≠ 0 →
      Nat.Coprime r (2 * s) := by
  intro r s hrs
  rw [Work.FIArea4.quadArrE] at hrs
  split_ifs at hrs with hcond
  · set z : GaussianInt := ⟨σ₁ * (r:ℤ), σ₂ * (s:ℤ)⟩ with hz
    have hb : β (Work.FIArea4.scalePt e z) ≠ 0 := by
      intro h0
      apply hrs
      rw [Work.FIArea4.S15red.S15strU_eq, h0, zero_mul, zero_mul]
    have hcop := hβ.coprime hb
    have hzre : z.re.natAbs = σ₁.natAbs * r := by
      rw [hz]; simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have hzim : z.im.natAbs = σ₂.natAbs * s := by
      rw [hz]; simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have hsr : (Work.FIArea4.scalePt e z).re.natAbs = e * z.re.natAbs := by
      rw [Work.FIArea4.scalePt_re, Int.natAbs_mul, Int.natAbs_natCast]
    have hsi : (Work.FIArea4.scalePt e z).im.natAbs = z.im.natAbs := by
      rw [Work.FIArea4.scalePt_im]
    have hr : r ∣ (Work.FIArea4.scalePt e z).re.natAbs := by
      rw [hsr, hzre]; exact ⟨e * σ₁.natAbs, by ring⟩
    have hs : 2 * s ∣ 2 * (Work.FIArea4.scalePt e z).im.natAbs := by
      rw [hsi, hzim]; exact ⟨σ₂.natAbs, by ring⟩
    exact (hcop.coprime_dvd_right hs).coprime_dvd_left hr
  · exact absurd rfl hrs

/-- **The four-quadrant reduction with the sign-quadrant index set `Q`.**  A restatement of
`Work.S15hybrid.EvarG_le_quad_shrunk` with the four sign combinations packaged as the Finset
`Work.FIArea4.S15red.Q = {(1,1),(1,-1),(-1,1),(-1,-1)}`, which is the form in which the quadrant
reduction is summed over in the §15 variance half. -/
lemma EvarG_le_sum_Q_of_prim (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (he : 1 ≤ e)
    (m : ℕ) (hm : 2 ≤ m) :
    Work.FIArea4.EvarG (Work.FITop.radN Pa) m (Work.FIArea4.S15strU β u t ℓ e)
      ≤ 4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
          Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
            (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
              (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2) := by
  have h := Work.S15hybrid.EvarG_le_quad_shrunk Pa φ β hβ u t ℓ e he m hm
  have hQ : (∑ σ ∈ Work.FIArea4.S15red.Q,
          Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
            (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
              (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2))
      = Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
          (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) (Work.FIArea4.S15strU β u t ℓ e) 1 1)
        + Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
          (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) (Work.FIArea4.S15strU β u t ℓ e) 1 (-1))
        + Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
          (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) (Work.FIArea4.S15strU β u t ℓ e) (-1) 1)
        + Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
          (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) (Work.FIArea4.S15strU β u t ℓ e) (-1) (-1)) := by
    simp [Work.FIArea4.S15red.Q, Finset.sum_insert, add_assoc]
  rw [hQ]
  exact h

/-- **The dyadic-stratum `d'`-sum of the stratum-`U` class variances against Proposition 14.1.**
Summing the stratum `d'`-index set `Work.S15crux.dset` by dyadic modulus block, applying the
Proposition-14.1 bracket `hCp` to each block, and regrouping gives the stated bound against the
dyadic bracket sum `Σ_k p14Bracket (2^k) (ReK Pa e) (SeK Pa) ε` and the quadrant-reduced
Prop.-14.1 energy `Σ_σ p14Ener (ReK Pa e) (SeK Pa) (quadArrE …)`. -/
theorem stratumDsetLe (Cp ε : ℝ)
    (hCp : ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      Work.FIPlan.Vvar R S D α ≤ Cp * Work.FIArea4.p14Bracket D R S ε * Work.FIArea4.p14Ener R S α)
    (Pa : Work.FITop.Params) (X j e : ℕ) (φ : ℝ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (hX : 1 ≤ X) (he : 1 ≤ e) :
    (∑ d' ∈ Work.S15crux.dset Pa X j e,
        Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * d') (Work.FIArea4.S15strU β u t ℓ e))
      ≤ 4 * Cp * (∑ k ∈ Work.S15crux.kset Pa X j e,
              Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
                (Work.FIArea4.S15red.SeK Pa) ε)
          * (∑ σ ∈ Work.FIArea4.S15red.Q,
              Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa)
                (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                  (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2)) := by
  classical
  set S := Work.FIArea4.S15strU β u t ℓ e with hSdef
  set Ene : ℤ × ℤ → ℝ := fun σ =>
      Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa)
        (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2) with hEnedef
  -- Step 1: the per-`d'` four-quadrant reduction, summed over the `d'`-index set.
  have hper : ∀ d' ∈ Work.S15crux.dset Pa X j e,
      Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * d') S
        ≤ 4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
            Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) (4 * d')
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2) := by
    intro d' hd'
    have hd'1 : 1 ≤ d' := by
      rw [Work.S15crux.dset, Finset.mem_filter, Finset.mem_Icc] at hd'
      exact hd'.1.1
    exact EvarG_le_sum_Q_of_prim Pa φ β hβ u t ℓ e he (4 * d') (by omega)
  have hstep1 : (∑ d' ∈ Work.S15crux.dset Pa X j e,
        Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * d') S)
      ≤ 4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
          ∑ d' ∈ Work.S15crux.dset Pa X j e,
            Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) (4 * d')
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2) := by
    calc (∑ d' ∈ Work.S15crux.dset Pa X j e, Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * d') S)
        ≤ ∑ d' ∈ Work.S15crux.dset Pa X j e,
            4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
              Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) (4 * d')
                (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2) :=
          Finset.sum_le_sum hper
      _ = 4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
            ∑ d' ∈ Work.S15crux.dset Pa X j e,
              Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) (4 * d')
                (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
  -- Step 2: dyadic decomposition of the `d'`-sum and the Prop.-14.1 bracket on each block.
  have hstep3 : (4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
          ∑ d' ∈ Work.S15crux.dset Pa X j e,
            Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) (4 * d')
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2))
      ≤ 4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
          ∑ k ∈ Work.S15crux.kset Pa X j e,
            Cp * Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
              (Work.FIArea4.S15red.SeK Pa) ε * Ene σ := by
    gcongr 4 * ?_
    refine Finset.sum_le_sum (fun σ hσ => ?_)
    refine le_trans (Work.S15crux.sum_dset_Evar_le_sum_kset_Vvar (Work.FIArea4.S15red.ReK Pa e)
      (Work.FIArea4.S15red.SeK Pa) (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2)
      Pa X j e) (Finset.sum_le_sum (fun k hk => ?_))
    exact hCp (2 ^ k) (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa)
      (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa) S σ.1 σ.2)
      Nat.one_le_two_pow (Work.FIArea4.S15red.one_le_ReK Pa e) (Work.FIArea4.S15red.one_le_SeK Pa)
      (quadArrE_strU_coprime Pa φ β hβ u t ℓ e σ.1 σ.2)
  -- Step 3: regroup the double sum into the product of the bracket sum and the energy sum.
  have hfinal : (4 * ∑ σ ∈ Work.FIArea4.S15red.Q,
          ∑ k ∈ Work.S15crux.kset Pa X j e,
            Cp * Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
              (Work.FIArea4.S15red.SeK Pa) ε * Ene σ)
      = 4 * Cp * (∑ k ∈ Work.S15crux.kset Pa X j e,
              Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
                (Work.FIArea4.S15red.SeK Pa) ε)
          * (∑ σ ∈ Work.FIArea4.S15red.Q, Ene σ) := by
    have hinner : ∀ σ : ℤ × ℤ,
        (∑ k ∈ Work.S15crux.kset Pa X j e,
            Cp * Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
              (Work.FIArea4.S15red.SeK Pa) ε * Ene σ)
        = (Cp * (∑ k ∈ Work.S15crux.kset Pa X j e,
              Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
                (Work.FIArea4.S15red.SeK Pa) ε)) * Ene σ := by
      intro σ
      rw [← Finset.sum_mul (Work.S15crux.kset Pa X j e)
            (fun k => Cp * Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
              (Work.FIArea4.S15red.SeK Pa) ε) (Ene σ),
          ← Finset.mul_sum (Work.S15crux.kset Pa X j e)
            (fun k => Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
              (Work.FIArea4.S15red.SeK Pa) ε) Cp]
    have hX2 : (∑ σ ∈ Work.FIArea4.S15red.Q,
          ∑ k ∈ Work.S15crux.kset Pa X j e,
            Cp * Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
              (Work.FIArea4.S15red.SeK Pa) ε * Ene σ)
        = (Cp * (∑ k ∈ Work.S15crux.kset Pa X j e,
              Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
                (Work.FIArea4.S15red.SeK Pa) ε)) * (∑ σ ∈ Work.FIArea4.S15red.Q, Ene σ) := by
      have h1 : (∑ σ ∈ Work.FIArea4.S15red.Q,
            ∑ k ∈ Work.S15crux.kset Pa X j e,
              Cp * Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
                (Work.FIArea4.S15red.SeK Pa) ε * Ene σ)
          = ∑ σ ∈ Work.FIArea4.S15red.Q,
              (Cp * (∑ k ∈ Work.S15crux.kset Pa X j e,
                Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
                  (Work.FIArea4.S15red.SeK Pa) ε)) * Ene σ :=
        Finset.sum_congr rfl (fun σ _ => hinner σ)
      rw [h1]
      exact (Finset.mul_sum Work.FIArea4.S15red.Q Ene
        (Cp * (∑ k ∈ Work.S15crux.kset Pa X j e,
          Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
            (Work.FIArea4.S15red.SeK Pa) ε))).symm
    rw [hX2]; ring
  exact le_trans hstep1 (le_trans hstep3 (le_of_eq hfinal))

end

end Work.FIArea4.A6R2
