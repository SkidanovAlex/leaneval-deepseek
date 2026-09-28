import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.LinearCount
import Submission.Work.HP.NA.gcdMinors2_mem_range_sub
import Submission.Work.HP.NA.exists_witness_of_mem_range
import Submission.Work.HP.NA.card_ideal_span_natCast

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HP.NA

/-- For a linear map `φ : (ι → R) →ₗ (R × R)` over `R = ZMod q`, the kernel and the range
satisfy `#ker · #range = q ^ #ι` (first isomorphism theorem at the level of cardinalities). -/
theorem card_ker_mul_card_range {ι : Type*} [Fintype ι] (q : ℕ)
    (φ : (ι → ZMod q) →ₗ[ZMod q] (ZMod q × ZMod q)) :
    Nat.card ↥(LinearMap.ker φ) * Nat.card ↥(LinearMap.range φ) = q ^ Fintype.card ι := by
  have hcard := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
  have hquot : Nat.card ((ι → ZMod q) ⧸ LinearMap.ker φ) = Nat.card ↥(LinearMap.range φ) :=
    Nat.card_congr (LinearMap.quotKerEquivRange φ).toEquiv
  have hdom : Nat.card (ι → ZMod q) = q ^ Fintype.card ι := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  rw [hquot, hdom] at hcard
  exact hcard.symm

theorem card_pair_kernel_le_gen {ι : Type*} [Fintype ι] {p r : ℕ} (hp : p.Prime)
    (hr : 1 ≤ r) (u v : ι → ℤ) (hu : ∃ i, IsUnit ((u i : ZMod (p ^ r)))) :
    Nat.card {a : ι → ZMod (p ^ r) //
        (∑ i, a i * ((u i : ℤ) : ZMod (p ^ r)) = 0) ∧
        (∑ i, a i * ((v i : ℤ) : ZMod (p ^ r)) = 0)}
      ≤ (p ^ r) ^ (Fintype.card ι - 2) * Nat.gcd (Work.HP.gcdMinors2 u v).natAbs (p ^ r) := by
  classical
  obtain ⟨i0, hu0⟩ := hu
  have hqpos : 0 < p ^ r := pow_pos hp.pos r
  haveI : NeZero (p ^ r) := ⟨hqpos.ne'⟩
  -- the right-hand side threshold
  set g : ℕ := Nat.gcd (Work.HP.gcdMinors2 u v).natAbs (p ^ r) with hgdef
  -- the multiplier turning `ū i₀` into `v̄ i₀`
  set c : ZMod (p ^ r) := (↑((hu0.unit)⁻¹) : ZMod (p ^ r)) * ((v i0 : ℤ) : ZMod (p ^ r))
    with hcdef
  have hxv : (↑((hu0.unit)⁻¹) : ZMod (p ^ r)) * ((u i0 : ℤ) : ZMod (p ^ r)) = 1 :=
    hu0.val_inv_mul
  have hc : c * ((u i0 : ℤ) : ZMod (p ^ r)) = ((v i0 : ℤ) : ZMod (p ^ r)) := by
    rw [hcdef, mul_assoc, mul_comm (((v i0 : ℤ) : ZMod (p ^ r))), ← mul_assoc, hxv, one_mul]
  -- the pair of linear functionals evaluating `u` and `v`
  set φ : (ι → ZMod (p ^ r)) →ₗ[ZMod (p ^ r)] (ZMod (p ^ r) × ZMod (p ^ r)) :=
    (Fintype.linearCombination (ZMod (p ^ r)) (fun i => ((u i : ℤ) : ZMod (p ^ r)))).prod
      (Fintype.linearCombination (ZMod (p ^ r)) (fun i => ((v i : ℤ) : ZMod (p ^ r))))
    with hφdef
  set S : Set (ι → ZMod (p ^ r)) :=
    {a | (∑ i, a i * ((u i : ℤ) : ZMod (p ^ r)) = 0) ∧
        (∑ i, a i * ((v i : ℤ) : ZMod (p ^ r)) = 0)} with hSdef
  -- the solution set is the kernel of `φ`
  have hker : Nat.card ↥S = Nat.card ↥(LinearMap.ker φ) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro a
    change ((∑ i, a i * ((u i : ℤ) : ZMod (p ^ r)) = 0) ∧
        (∑ i, a i * ((v i : ℤ) : ZMod (p ^ r)) = 0)) ↔ a ∈ LinearMap.ker φ
    have hpair : φ a = ((∑ i, a i * ((u i : ℤ) : ZMod (p ^ r))),
        (∑ i, a i * ((v i : ℤ) : ZMod (p ^ r)))) := by
      simp only [φ, LinearMap.prod_apply, Function.prod_apply,
        Fintype.linearCombination_apply, smul_eq_mul]
    rw [LinearMap.mem_ker, hpair]
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]; rfl
    · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hkey : Nat.card ↥S * Nat.card ↥(LinearMap.range φ) = (p ^ r) ^ Fintype.card ι := by
    rw [hker]
    exact card_ker_mul_card_range (p ^ r) φ
  -- a sum of a `Pi.single` against any vector
  have hsingle : ∀ (w : ι → ZMod (p ^ r)) (x : ZMod (p ^ r)),
      (∑ i, (Pi.single i0 x : ι → ZMod (p ^ r)) i * w i) = x * w i0 := by
    intro w x
    rw [Finset.sum_eq_single i0]
    · rw [Pi.single_eq_same]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i0) h
  -- `(1, c)` belongs to the range
  have h1c : ((1 : ZMod (p ^ r)), c) ∈ LinearMap.range φ := by
    refine ⟨Pi.single i0 (↑((hu0.unit)⁻¹) : ZMod (p ^ r)), ?_⟩
    have hpair : φ (Pi.single i0 (↑((hu0.unit)⁻¹) : ZMod (p ^ r)))
        = ((↑((hu0.unit)⁻¹) : ZMod (p ^ r)) * ((u i0 : ℤ) : ZMod (p ^ r)),
           (↑((hu0.unit)⁻¹) : ZMod (p ^ r)) * ((v i0 : ℤ) : ZMod (p ^ r))) := by
      simp only [φ, LinearMap.prod_apply, Function.prod_apply,
        Fintype.linearCombination_apply, smul_eq_mul]
      rw [hsingle, hsingle]
    rw [hpair, hxv, hcdef]
  -- `(0, g)` belongs to the range, via the two delegated lemmas
  have hmemψ : (g : ZMod (p ^ r)) ∈ LinearMap.range
      (Fintype.linearCombination (ZMod (p ^ r))
        (fun i => ((v i : ℤ) : ZMod (p ^ r)) - c * ((u i : ℤ) : ZMod (p ^ r)))) :=
    gcdMinors2_mem_range_sub u v i0 hu0 hc
  have h0g : ((0 : ZMod (p ^ r)), (g : ZMod (p ^ r))) ∈ LinearMap.range φ := by
    obtain ⟨a, ha1, ha2⟩ := exists_witness_of_mem_range u v i0 hu0 hc hmemψ
    refine ⟨a, ?_⟩
    have hφa : φ a = ((0 : ZMod (p ^ r)), (g : ZMod (p ^ r))) := by
      have hpair : φ a = ((∑ i, a i * ((u i : ℤ) : ZMod (p ^ r))),
          (∑ i, a i * ((v i : ℤ) : ZMod (p ^ r)))) := by
        simp only [φ, LinearMap.prod_apply, Function.prod_apply,
        Fintype.linearCombination_apply, smul_eq_mul]
      rw [hpair, ha1, ha2]
    rw [hφa]
  -- the injection `ZMod q × (g) ↪ range φ`
  set F : ZMod (p ^ r) × ↥(Ideal.span ({(g : ZMod (p ^ r))} : Set (ZMod (p ^ r)))) →
      ↥(LinearMap.range φ) :=
    fun y => ⟨(y.1, c * y.1 + (y.2 : ZMod (p ^ r))), by
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp y.2.2
      have hde : (y.1, c * y.1 + (y.2 : ZMod (p ^ r)))
          = y.1 • ((1 : ZMod (p ^ r)), c)
            + z • ((0 : ZMod (p ^ r)), (g : ZMod (p ^ r))) := by
        simp [Prod.smul_mk, smul_eq_mul, hz, mul_comm]
      rw [hde]
      exact Submodule.add_mem _ (Submodule.smul_mem _ y.1 h1c) (Submodule.smul_mem _ z h0g)⟩
    with hFdef
  have hFinj : Function.Injective F := by
    rintro ⟨s, y⟩ ⟨s', y'⟩ h
    have h1 : s = s' :=
      congrArg (fun t : ↥(LinearMap.range φ) => (t : ZMod (p ^ r) × ZMod (p ^ r)).1) h
    have h2 : (y : ZMod (p ^ r)) = (y' : ZMod (p ^ r)) := by
      have h3 : c * s + (y : ZMod (p ^ r)) = c * s' + (y' : ZMod (p ^ r)) :=
        congrArg (fun t : ↥(LinearMap.range φ) => (t : ZMod (p ^ r) × ZMod (p ^ r)).2) h
      rw [h1] at h3
      exact add_left_cancel h3
    exact Prod.ext h1 (Subtype.ext h2)
  have hgdvd : g ∣ p ^ r := by
    rw [hgdef]; exact Nat.gcd_dvd_right _ _
  have hge : (p ^ r) * ((p ^ r) / g) ≤ Nat.card ↥(LinearMap.range φ) := by
    have h := Nat.card_le_card_of_injective F hFinj
    rw [Nat.card_prod, Nat.card_zmod, card_ideal_span_natCast (p ^ r) g hqpos hgdvd] at h
    exact h
  -- arithmetic
  have hmul : Nat.card ↥S * ((p ^ r) * (p ^ r)) ≤ (p ^ r) ^ (Fintype.card ι) * g := by
    have step1 : Nat.card ↥S * ((p ^ r) * ((p ^ r) / g)) ≤ (p ^ r) ^ (Fintype.card ι) := by
      have h := Nat.mul_le_mul_left (Nat.card ↥S) hge
      rwa [hkey] at h
    have step2 : Nat.card ↥S * ((p ^ r) * ((p ^ r) / g)) * g ≤ (p ^ r) ^ (Fintype.card ι) * g :=
      Nat.mul_le_mul_right g step1
    have hinner : ((p ^ r) * ((p ^ r) / g)) * g = (p ^ r) * (p ^ r) := by
      rw [mul_assoc (p ^ r) ((p ^ r) / g) g, Nat.div_mul_cancel hgdvd]
    have heq : Nat.card ↥S * ((p ^ r) * ((p ^ r) / g)) * g
        = Nat.card ↥S * ((p ^ r) * (p ^ r)) := by
      rw [mul_assoc (Nat.card ↥S) ((p ^ r) * ((p ^ r) / g)) g, hinner]
    rwa [heq] at step2
  by_cases hN : Fintype.card ι ≤ 1
  · -- at most one index: the bound is `#S ≤ g`
    have hqN : (p ^ r) ^ (Fintype.card ι) ≤ p ^ r := by
      calc (p ^ r) ^ (Fintype.card ι) ≤ (p ^ r) ^ 1 := Nat.pow_le_pow_right hqpos hN
        _ = p ^ r := pow_one _
    have h4 : Nat.card ↥S * (p ^ r) * (p ^ r) ≤ g * (p ^ r) := by
      calc Nat.card ↥S * (p ^ r) * (p ^ r) = Nat.card ↥S * ((p ^ r) * (p ^ r)) := by
            rw [mul_assoc]
        _ ≤ (p ^ r) ^ (Fintype.card ι) * g := hmul
        _ ≤ (p ^ r) * g := Nat.mul_le_mul_right g hqN
        _ = g * (p ^ r) := by rw [mul_comm]
    have hle : Nat.card ↥S ≤ g := by
      have h5 : Nat.card ↥S * (p ^ r) ≤ g := Nat.le_of_mul_le_mul_right h4 hqpos
      exact le_trans (Nat.le_mul_of_pos_right _ hqpos) h5
    have hN0 : Fintype.card ι - 2 = 0 := by omega
    calc Nat.card ↥S ≤ g := hle
      _ = (p ^ r) ^ (Fintype.card ι - 2) * g := by rw [hN0, pow_zero, one_mul]
  · -- at least two indices: cancel `(p^r)^2`
    have hN2 : 2 ≤ Fintype.card ι := by
      have : 1 < Fintype.card ι := not_le.mp hN
      omega
    have hpow : (p ^ r) ^ (Fintype.card ι)
        = (p ^ r) ^ (Fintype.card ι - 2) * ((p ^ r) * (p ^ r)) := by
      rw [← pow_two, ← pow_add]
      congr 1
      omega
    have h5 : Nat.card ↥S * ((p ^ r) * (p ^ r))
        ≤ ((p ^ r) ^ (Fintype.card ι - 2) * g) * ((p ^ r) * (p ^ r)) := by
      calc Nat.card ↥S * ((p ^ r) * (p ^ r)) ≤ (p ^ r) ^ (Fintype.card ι) * g := hmul
        _ = ((p ^ r) ^ (Fintype.card ι - 2) * g) * ((p ^ r) * (p ^ r)) := by
              rw [hpow]; ring
    exact Nat.le_of_mul_le_mul_right h5 (mul_pos hqpos hqpos)

end Work.HP.NA
