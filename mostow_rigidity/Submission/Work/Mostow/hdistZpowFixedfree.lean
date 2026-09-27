import Mathlib
import Submission.Work.Mostow.axisDichotomy

/-!
# Displacement of powers of a fixed point free isometry of `ℍ¹`

`PO 1 1` is the isometry group of `ℍ¹`.  A fixed point free element `g₀` is a translation, and in
the signed-distance chart `sc` the induced map `Phi g₀` is `x ↦ x + c` with `c = Phi g₀ 0 ≠ 0`.
Composing, the `k`-th power is `x ↦ x + k c`, so the hyperbolic displacement of any point under
`g₀ ^ k` is exactly `|k| · |c| = |k| · hdist 0 (g₀ • 0)`.

This is the elementary input used in the base-case analysis of the discrete subgroup `Γ ≤ PO 1 1`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

namespace HdistZpowFixedfreeAux

open AxisDich

/-- A fixed point free isometry of `ℍ¹` acts by a translation in the signed coordinate. -/
lemma Phi_trans_of_free (hI : HypIsoData 1) (g : PO 1 1)
    (hg : ∀ x : E 1, g • x ≠ x) (x : ℝ) : Phi g x = Phi g 0 + x := by
  rcases Phi_form hI g with ⟨c, hc | hc⟩
  · rw [hc x, hc 0]; ring
  · exfalso
    have hfix : g • pt (c / 2) = pt (c / 2) := by
      rw [Phi_fix_iff hI g (pt (c / 2)), sc_pt, hc (c / 2)]
      ring
    exact hg (pt (c / 2)) hfix

/-- The inverse of a translation `x ↦ d + x` acts by `x ↦ -d + x`. -/
lemma Phi_inv_form (hA : POBasic 1) (h : PO 1 1) (d : ℝ)
    (hd : ∀ x, Phi h x = d + x) : ∀ x, Phi h⁻¹ x = -d + x := by
  intro y
  have hz : Phi h (y - d) = y := by rw [hd]; ring
  calc Phi h⁻¹ y = Phi h⁻¹ (Phi h (y - d)) := by rw [hz]
    _ = Phi (h⁻¹ * h) (y - d) := by rw [Phi_mul hA]; rfl
    _ = Phi 1 (y - d) := by rw [inv_mul_cancel]
    _ = y - d := by rw [Phi_one hA]; rfl
    _ = -d + y := by ring

/-- Powers of a fixed point free element act by `x ↦ n · c + x` in the signed coordinate. -/
lemma Phi_pow_nat (hA : POBasic 1) (hI : HypIsoData 1) (g : PO 1 1)
    (hg : ∀ x : E 1, g • x ≠ x) (n : ℕ) (x : ℝ) :
    Phi (g ^ n) x = (n : ℝ) * Phi g 0 + x := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero, Phi_one hA]
      simp
  | succ n ih =>
      have h1 : Phi (g ^ (n + 1)) x = Phi (g ^ n) (Phi g x) := by
        rw [pow_succ, Phi_mul hA]; rfl
      rw [h1, Phi_trans_of_free hI g hg x, ih]
      push_cast
      ring

/-- Integer powers of a fixed point free element act by `x ↦ k · c + x` in the signed coordinate. -/
lemma Phi_zpow (hA : POBasic 1) (hI : HypIsoData 1) (g : PO 1 1)
    (hg : ∀ x : E 1, g • x ≠ x) (k : ℤ) (x : ℝ) :
    Phi (g ^ k) x = (k : ℝ) * Phi g 0 + x := by
  rcases Int.eq_nat_or_neg k with ⟨n, hn | hn⟩
  · subst hn
    rw [zpow_natCast]
    exact Phi_pow_nat hA hI g hg n x
  · subst hn
    have hz : (g : PO 1 1) ^ (-(n : ℤ)) = (g ^ n)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hz]
    rw [Phi_inv_form hA (g ^ n) ((n : ℝ) * Phi g 0) (Phi_pow_nat hA hI g hg n) x]
    push_cast
    ring

end HdistZpowFixedfreeAux

open HdistZpowFixedfreeAux AxisDich

theorem hdistZpowFixedfree
    (hA : Submission.Mostow.POActionProp 1) (hI : Submission.Mostow.HypIsometryProp 1)
    (g₀ : LeanEval.Geometry.MostowRigidity.PO 1 1)
    (hgf : ∀ x : Submission.Mostow.E 1, g₀ • x ≠ x) (v : Submission.Mostow.E 1) (k : ℤ) :
    Submission.Mostow.hdist v ((g₀ ^ k) • v)
      = (|(k : ℝ)|) * Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) := by
  have hA' : POBasic 1 := POBasic.ofProp hA
  have hI' : HypIsoData 1 := HypIsoData.ofProp hI
  obtain ⟨c, hc | hc⟩ := Phi_form hI' g₀
  · have hgc : Phi g₀ 0 = c := by rw [hc 0]; ring
    have hmain : ∀ x : ℝ, Phi (g₀ ^ k) x = (k : ℝ) * c + x := by
      intro x
      rw [Phi_zpow hA' hI' g₀ hgf k x, hgc]
    have hsc : sc ((g₀ ^ k) • v) = (k : ℝ) * c + sc v := by
      have h := hmain (sc v)
      rwa [show Phi (g₀ ^ k) (sc v) = sc ((g₀ ^ k) • v) from by
        show sc ((g₀ ^ k) • pt (sc v)) = sc ((g₀ ^ k) • v)
        rw [pt_sc]] at h
    have hd0 : hdist (0 : E 1) (g₀ • (0 : E 1)) = |c| := by
      rw [hdist_zero_eq_sc]
      have h3 : sc (g₀ • (0 : E 1)) = c := by
        rw [show (0 : E 1) = pt 0 from pt_zero.symm]
        exact hgc
      rw [h3]
    calc hdist v ((g₀ ^ k) • v)
        = |sc v - sc ((g₀ ^ k) • v)| := hdist_eq_sc v ((g₀ ^ k) • v)
      _ = |(k : ℝ) * c| := by
            rw [hsc, abs_sub_comm]
            congr 1
            ring
      _ = |(k : ℝ)| * |c| := abs_mul _ _
      _ = |(k : ℝ)| * hdist (0 : E 1) (g₀ • (0 : E 1)) := by rw [hd0]
  · exfalso
    have hfix : g₀ • pt (c / 2) = pt (c / 2) := by
      rw [Phi_fix_iff hI' g₀ (pt (c / 2)), sc_pt, hc (c / 2)]
      ring
    exact hgf (pt (c / 2)) hfix

end Work.Mostow
