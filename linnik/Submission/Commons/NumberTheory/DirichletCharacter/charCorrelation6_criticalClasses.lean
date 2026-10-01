import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_criticalClasses
import Submission.Commons.NumberTheory.ZMod.digit_decomposition_bijective

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators
open CharCorr

variable {p e : ℕ}

theorem coset_sum3 [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (c d : Fin 3 → ℕ)
    (y : ZMod (p ^ (e - 1))) :
    (∑ t : ZMod p,
        χ (∏ l : Fin 3, (digitPt p e y t + (c l : ZMod (p^e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitPt p e y t + (d l : ZMod (p^e))))))
      = (p : ℂ) * (if ((∑ l : Fin 3, (((y.val : ℕ) : ZMod p) + (c l : ZMod p))⁻¹)
                        - (∑ l : Fin 3, (((y.val : ℕ) : ZMod p) + (d l : ZMod p))⁻¹) = 0)
                   then χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
                        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e)))))
                   else 0) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp_pos.ne'⟩
  haveI : NeZero p := ⟨hp_pos.ne'⟩
  set ζ : ℂ := χ ((1 + p ^ (e-1) : ℕ) : ZMod (p^e)) with hζdef
  have hζ : IsPrimitiveRoot ζ p := chi_one_add_primePow_isPrimitiveRoot p e hp2 he χ hχ
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζp
  have hψapply : ∀ s : ZMod p, ψ s = ζ ^ (s.val) := fun s => AddChar.zmodChar_apply hζp s
  have hringChar : 0 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hp_pos
  set w : ℕ → ZMod p := fun u => (((y.val : ℕ) : ZMod p) + (u : ZMod p))⁻¹ with hw
  set D : ZMod p := (∑ l : Fin 3, w (c l)) - (∑ l : Fin 3, w (d l)) with hD
  have htw : ∀ (u : ℕ) (t : ZMod p), χ (digitPt p e y t + (u : ZMod (p^e)))
      = χ (digitLift p e y + (u : ZMod (p^e))) * ψ (t * w u) := by
    intro u t
    rw [twist_pt (p := p) (e := e) he χ y u t, hψapply, ← hζdef]
  have htw' : ∀ (u : ℕ) (t : ZMod p), (starRingEnd ℂ) (χ (digitPt p e y t + (u : ZMod (p^e))))
      = (starRingEnd ℂ) (χ (digitLift p e y + (u : ZMod (p^e)))) * ψ (t * (-(w u))) := by
    intro u t
    rw [htw u t, map_mul]
    rw [show (starRingEnd ℂ) (ψ (t * w u)) = ψ (-(t * w u)) from by
      rw [AddChar.starComp_apply (φ := ψ) hringChar (t * w u)]
      rw [AddChar.inv_apply]]
    congr 1
    ring
  have hchi_prod : ∀ (t : ZMod p) (g : Fin 3 → ℕ),
      χ (∏ l : Fin 3, (digitPt p e y t + (g l : ZMod (p^e))))
      = (∏ l : Fin 3, χ (digitLift p e y + (g l : ZMod (p^e))))
        * ∏ l : Fin 3, ψ (t * w (g l)) := by
    intro t g
    rw [map_prod χ (fun l => digitPt p e y t + (g l : ZMod (p^e))) Finset.univ]
    rw [Finset.prod_congr rfl (fun l _ => htw (g l) t)]
    rw [Finset.prod_mul_distrib]
  have hstar_prod : ∀ (t : ZMod p) (g : Fin 3 → ℕ),
      (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitPt p e y t + (g l : ZMod (p^e)))))
      = (∏ l : Fin 3, (starRingEnd ℂ) (χ (digitLift p e y + (g l : ZMod (p^e)))))
        * ∏ l : Fin 3, ψ (t * (-(w (g l)))) := by
    intro t g
    rw [map_prod χ (fun l => digitPt p e y t + (g l : ZMod (p^e))) Finset.univ]
    rw [map_prod (starRingEnd ℂ) (fun l => χ (digitPt p e y t + (g l : ZMod (p^e)))) Finset.univ]
    rw [Finset.prod_congr rfl (fun l _ => htw' (g l) t)]
    rw [Finset.prod_mul_distrib]
  have hψc : ∀ t : ZMod p, (∏ l : Fin 3, ψ (t * w (c l))) = ψ (t * (∑ l : Fin 3, w (c l))) := by
    intro t
    rw [Fin.prod_univ_three, Fin.sum_univ_three]
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hψd : ∀ t : ZMod p, (∏ l : Fin 3, ψ (t * (-(w (d l))))) = ψ (t * (-(∑ l : Fin 3, w (d l)))) := by
    intro t
    rw [Fin.prod_univ_three, Fin.sum_univ_three]
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hsummand : ∀ t : ZMod p,
      χ (∏ l : Fin 3, (digitPt p e y t + (c l : ZMod (p^e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitPt p e y t + (d l : ZMod (p^e)))))
      = (χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e))))))
        * ψ (t * D) := by
    intro t
    have hL : χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
        = ∏ l : Fin 3, χ (digitLift p e y + (c l : ZMod (p^e))) :=
      map_prod χ (fun l => digitLift p e y + (c l : ZMod (p^e))) Finset.univ
    have hR : (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e)))))
        = ∏ l : Fin 3, (starRingEnd ℂ) (χ (digitLift p e y + (d l : ZMod (p^e)))) := by
      rw [map_prod χ (fun l => digitLift p e y + (d l : ZMod (p^e))) Finset.univ]
      exact map_prod (starRingEnd ℂ) (fun l => χ (digitLift p e y + (d l : ZMod (p^e)))) Finset.univ
    have hcombine : ψ (t * (∑ l : Fin 3, w (c l))) * ψ (t * (-(∑ l : Fin 3, w (d l))))
        = ψ (t * D) := by
      rw [← AddChar.map_add_eq_mul, hD]
      congr 1
      ring
    rw [hchi_prod t c, hstar_prod t d, hψc t, hψd t, hL, hR]
    rw [show (∏ l : Fin 3, χ (digitLift p e y + (c l : ZMod (p^e))))
          * ψ (t * (∑ l : Fin 3, w (c l)))
          * ((∏ l : Fin 3, (starRingEnd ℂ) (χ (digitLift p e y + (d l : ZMod (p^e)))))
              * ψ (t * (-(∑ l : Fin 3, w (d l)))))
        = (∏ l : Fin 3, χ (digitLift p e y + (c l : ZMod (p^e))))
          * (∏ l : Fin 3, (starRingEnd ℂ) (χ (digitLift p e y + (d l : ZMod (p^e)))))
          * (ψ (t * (∑ l : Fin 3, w (c l))) * ψ (t * (-(∑ l : Fin 3, w (d l)))))
        from by ring]
    rw [hcombine]
  calc (∑ t : ZMod p,
        χ (∏ l : Fin 3, (digitPt p e y t + (c l : ZMod (p^e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitPt p e y t + (d l : ZMod (p^e))))))
      = ∑ t : ZMod p,
          (χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e))))))
          * ψ (t * D) := Finset.sum_congr rfl (fun t _ => hsummand t)
    _ = (χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e))))))
          * ∑ t : ZMod p, ψ (t * D) := by rw [Finset.mul_sum]
    _ = (χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e))))))
          * (if D = 0 then ((p : ℕ) : ℂ) else 0) := by
        rw [show (∑ t : ZMod p, ψ (t * D)) = ∑ t : ZMod p, ζ ^ ((t*D).val) from
          Finset.sum_congr rfl (fun t _ => hψapply (t*D))]
        rw [geom_sum_zmodChar hζ D]
    _ = (p : ℂ) * (if D = 0
          then χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e)))))
          else 0) := by
        split_ifs <;> ring
    _ = (p : ℂ) * (if ((∑ l : Fin 3, (((y.val : ℕ) : ZMod p) + (c l : ZMod p))⁻¹)
                        - (∑ l : Fin 3, (((y.val : ℕ) : ZMod p) + (d l : ZMod p))⁻¹) = 0)
                   then χ (∏ l : Fin 3, (digitLift p e y + (c l : ZMod (p^e))))
                        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (digitLift p e y + (d l : ZMod (p^e)))))
                   else 0) := by
        rw [hD]

theorem charCorrelation6_criticalClasses {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (e : ℕ) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) :
    (∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e))))))
      = (p : ℂ) * ∑ r : ZMod p,
          (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
           then ∑ z : ZMod (p ^ (e - 2)),
                  χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                      + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
                  * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                      + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
           else 0) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  haveI : NeZero p := ⟨hp_pos.ne'⟩
  haveI : NeZero (p^e) := ⟨pow_ne_zero e hp_pos.ne'⟩
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero (e-1) hp_pos.ne'⟩
  haveI : NeZero (p^(e-2)) := ⟨pow_ne_zero (e-2) hp_pos.ne'⟩
  set F : ZMod (p^e) → ℂ := fun x => χ (∏ l : Fin 3, (x + (a l : ZMod (p^e))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^e))))) with hF
  set critY : ZMod (p^(e-1)) → Prop := fun y =>
      (∑ l : Fin 3, (((y.val : ℕ) : ZMod p) + (a l : ZMod p))⁻¹)
        - (∑ l : Fin 3, (((y.val : ℕ) : ZMod p) + (b l : ZMod p))⁻¹) = 0
      with hcritY
  have hB1 := Commons.NumberTheory.ZMod.digit_decomposition_bijective p (e - 1) hp_pos
  rw [show e - 1 + 1 = e by omega] at hB1
  let E1 : ZMod (p ^ (e - 1)) × ZMod p ≃ ZMod (p ^ e) :=
    Equiv.ofBijective (fun yt : ZMod (p ^ (e - 1)) × ZMod p =>
      ((yt.1.val : ℕ) : ZMod (p ^ e)) +
        ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) * ((yt.2.val : ℕ) : ZMod (p ^ e))) hB1
  have hE1 : ∀ yt : ZMod (p^(e-1)) × ZMod p, E1 yt = digitPt p e yt.1 yt.2 := by
    intro yt
    show ((yt.1.val : ℕ) : ZMod (p ^ e)) +
        ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) * ((yt.2.val : ℕ) : ZMod (p ^ e))
        = ((yt.1.val : ℕ) : ZMod (p ^ e)) + ((p ^ (e - 1) * yt.2.val : ℕ) : ZMod (p ^ e))
    rw [Nat.cast_mul]
  have hB2 := lowDigit_decomposition_bijective p (e - 2) hp_pos
  rw [show e - 2 + 1 = e - 1 by omega] at hB2
  let E2 : ZMod p × ZMod (p ^ (e - 2)) ≃ ZMod (p ^ (e - 1)) :=
    Equiv.ofBijective (fun rz : ZMod p × ZMod (p ^ (e - 2)) =>
      ((rz.1.val + p * rz.2.val : ℕ) : ZMod (p ^ (e - 1)))) hB2
  have hE2apply : ∀ rz : ZMod p × ZMod (p ^ (e - 2)),
      E2 rz = ((rz.1.val + p * rz.2.val : ℕ) : ZMod (p ^ (e - 1))) := fun rz => rfl
  have hE2bound : ∀ rz : ZMod p × ZMod (p^(e-2)), rz.1.val + p * rz.2.val < p^(e-1) := by
    intro rz
    have h1 : rz.1.val < p := ZMod.val_lt rz.1
    have h2 : rz.2.val < p^(e-2) := ZMod.val_lt rz.2
    calc rz.1.val + p * rz.2.val < p + p * rz.2.val := Nat.add_lt_add_right h1 _
      _ = p * (rz.2.val + 1) := by ring
      _ ≤ p * p^(e-2) := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr h2)
      _ = p^(e-1) := by rw [← pow_succ', show e - 2 + 1 = e - 1 by omega]
  have hE2val : ∀ rz : ZMod p × ZMod (p ^ (e - 2)), (E2 rz).val = rz.1.val + p * rz.2.val := by
    intro rz
    rw [hE2apply, ZMod.val_natCast, Nat.mod_eq_of_lt (hE2bound rz)]
  have hE2red : ∀ rz : ZMod p × ZMod (p ^ (e - 2)), (((E2 rz).val : ℕ) : ZMod p) = rz.1 := by
    intro rz
    rw [hE2val, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  have hE2lift : ∀ rz : ZMod p × ZMod (p ^ (e - 2)),
      digitLift p e (E2 rz) =
        ((rz.1.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((rz.2.val : ℕ) : ZMod (p^e)) := by
    intro rz
    simp only [digitLift]
    rw [hE2val]
    push_cast
    ring
  have hcritYZ : ∀ rz : ZMod p × ZMod (p^(e-2)),
      (critY (E2 rz) ↔ (∑ l : Fin 3, (rz.1 + (a l : ZMod p))⁻¹)
              - (∑ l : Fin 3, (rz.1 + (b l : ZMod p))⁻¹) = 0) := by
    intro rz
    show (∑ l : Fin 3, ((((E2 rz).val : ℕ) : ZMod p) + (a l : ZMod p))⁻¹)
        - (∑ l : Fin 3, ((((E2 rz).val : ℕ) : ZMod p) + (b l : ZMod p))⁻¹) = 0
      ↔ (∑ l : Fin 3, (rz.1 + (a l : ZMod p))⁻¹)
              - (∑ l : Fin 3, (rz.1 + (b l : ZMod p))⁻¹) = 0
    rw [hE2red rz]
  have hstep2 : ∀ y : ZMod (p^(e-1)), (∑ t : ZMod p, F (E1 (y, t))) =
      (p : ℂ) * (if critY y then F (digitLift p e y) else 0) := by
    intro y
    have h1 : (∑ t : ZMod p, F (E1 (y, t))) = ∑ t : ZMod p, F (digitPt p e y t) :=
      Finset.sum_congr rfl (fun t _ => by rw [hE1])
    rw [h1]
    have h2 := coset_sum3 (p := p) (e := e) hp2 he χ hχ a b y
    simp only [hF, hcritY, digitLift, digitPt]
    exact h2
  have key : (∑ x : ZMod (p^e), F x) = (p : ℂ) * ∑ r : ZMod p,
          (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
           then ∑ z : ZMod (p ^ (e - 2)),
                  χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a l : ℕ)))
                  * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b l : ℕ))))
           else 0) := by
    calc (∑ x : ZMod (p^e), F x)
        = ∑ yt : ZMod (p^(e-1)) × ZMod p, F (E1 yt) :=
          (Fintype.sum_equiv E1 (fun yt => F (E1 yt)) F (fun yt => rfl)).symm
      _ = ∑ y : ZMod (p^(e-1)), ∑ t : ZMod p, F (E1 (y, t)) := Fintype.sum_prod_type _
      _ = ∑ y : ZMod (p^(e-1)), (p : ℂ) * (if critY y then F (digitLift p e y) else 0) :=
          Finset.sum_congr rfl (fun y _ => hstep2 y)
      _ = (p : ℂ) * ∑ y : ZMod (p^(e-1)), (if critY y then F (digitLift p e y) else 0) := by
          rw [Finset.mul_sum]
      _ = (p : ℂ) * ∑ rz : ZMod p × ZMod (p^(e-2)),
            (if critY (E2 rz) then F (digitLift p e (E2 rz)) else 0) := by
          congr 1
          exact (Fintype.sum_equiv E2
            (fun rz : ZMod p × ZMod (p^(e-2)) =>
              if critY (E2 rz) then F (digitLift p e (E2 rz)) else 0)
            (fun y => if critY y then F (digitLift p e y) else 0)
            (fun rz => rfl)).symm
      _ = (p : ℂ) * ∑ rz : ZMod p × ZMod (p^(e-2)),
            (if (∑ l : Fin 3, (rz.1 + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (rz.1 + (b l : ZMod p))⁻¹) = 0
             then F (digitLift p e (E2 rz)) else 0) := by
          congr 1
          refine Finset.sum_congr rfl (fun rz _ => ?_)
          by_cases h : (∑ l : Fin 3, (rz.1 + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (rz.1 + (b l : ZMod p))⁻¹) = 0
          · rw [if_pos ((hcritYZ rz).mpr h), if_pos h]
          · rw [if_neg (fun hh => h ((hcritYZ rz).mp hh)), if_neg h]
      _ = (p : ℂ) * ∑ r : ZMod p, ∑ z : ZMod (p^(e-2)),
            (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
             then F (digitLift p e (E2 (r, z))) else 0) := by
          rw [Fintype.sum_prod_type]
      _ = (p : ℂ) * ∑ r : ZMod p,
            (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
             then ∑ z : ZMod (p^(e-2)), F (digitLift p e (E2 (r, z))) else 0) := by
          congr 1
          refine Finset.sum_congr rfl (fun r _ => ?_)
          by_cases h : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0 <;> simp [h]
      _ = (p : ℂ) * ∑ r : ZMod p,
            (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
             then ∑ z : ZMod (p ^ (e - 2)),
                    χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a l : ℕ)))
                    * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b l : ℕ))))
             else 0) := by
          congr 1
          refine Finset.sum_congr rfl (fun r _ => ?_)
          by_cases h : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
          · rw [if_pos h, if_pos h]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            rw [hE2lift]
          · rw [if_neg h, if_neg h]
  rw [show (∑ x : ZMod (p^e), χ (∏ l : Fin 3, (x + (a l : ZMod (p^e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^e))))))
      = ∑ x : ZMod (p^e), F x from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [hF]]
  exact key

end Commons.NumberTheory.DirichletCharacter
