import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential
import Submission.Work.FTS.RegExportIface.RXT.LeafDefs
import Submission.Work.FTS_RegExport.RXT.cone_max_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.cone_induction` — leaf port (module `LeafAux.cone_induction`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.
Proof ported verbatim from the `Work.FTS_RegExport` mirror area; this module deliberately
does **not** import `Leaves` (which imports it), so the cycle is broken.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false


open Work.FTS_RegExport.RXT.ConeAux

theorem cone_induction {n : ℕ} {φ : Fin n → ℝ → ℝ → ℝ → ℝ} {T A C F K₀ : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C) (hF : 0 ≤ F) (hK₀ : 0 ≤ K₀)
    (hcont : ∀ k s ψ, ContinuousOn (fun τ => φ k s ψ τ) (Set.Icc 0 T))
    (h0 : ∀ k s ψ, |φ k s ψ 0| ≤ K₀)
    (hstep : Work.FTS.RegExportIface.RXT.ConeStep n φ T A C F) :
    ∀ k s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, |φ k s ψ τ| ≤ Real.exp (2 * C * τ) * (K₀ + τ * F) := by
  intro k₀ s₀ ψ₀ τ₀ hτ₀
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Fin.elim0 k₀
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases eq_or_lt_of_le hτ₀.1 with h0τ | hpos
  · rw [← h0τ]
    simpa using h0 k₀ s₀ ψ₀
  suffices hmain : ∀ η : ℝ, 0 < η →
      |φ k₀ s₀ ψ₀ τ₀| ≤ Real.exp (2 * C * τ₀) * (K₀ + τ₀ * (F + η)) by
    have hE : 0 < Real.exp (2 * C * τ₀) := Real.exp_pos _
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hden : 0 < Real.exp (2 * C * τ₀) * τ₀ := mul_pos hE hpos
    have h1 := hmain (ε / (Real.exp (2 * C * τ₀) * τ₀)) (div_pos hε hden)
    have halg : Real.exp (2 * C * τ₀) *
        (K₀ + τ₀ * (F + ε / (Real.exp (2 * C * τ₀) * τ₀)))
        = Real.exp (2 * C * τ₀) * (K₀ + τ₀ * F) + ε := by
      field_simp
      ring
    rw [halg] at h1
    linarith
  intro η hη
  have hFη : 0 ≤ F + η := by linarith
  -- the radius of the box on which the step hypothesis is invoked
  set Rb : ℝ := |s₀| + |ψ₀| + A * τ₀ + 1 with hRbdef
  obtain ⟨h₁, h₁pos, hstep₁⟩ := hstep Rb η hη
  -- the mesh
  obtain ⟨N, hNlt⟩ := exists_nat_gt (max (τ₀ / h₁) (2 * C * τ₀))
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le (div_pos hpos h₁pos) (le_max_left _ _)) hNlt.le
  set h : ℝ := τ₀ / (N : ℝ) with hhh
  have hhpos : 0 < h := div_pos hpos hNpos
  have hNh : (N : ℝ) * h = τ₀ := by rw [hhh]; field_simp
  have ht_eq : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by
    intro k; push_cast; ring
  have hh_lt : h < h₁ := by
    have h2 : τ₀ / h₁ < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hNlt
    have h3 : τ₀ < (N : ℝ) * h₁ := (div_lt_iff₀ h₁pos).mp h2
    rw [hhh, div_lt_iff₀ hNpos]
    linarith
  have hCh : C * h ≤ 1 / 2 := by
    have h2 : 2 * C * τ₀ < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNlt
    rw [hhh, show C * (τ₀ / (N : ℝ)) = (C * τ₀) / (N : ℝ) by ring, div_le_iff₀ hNpos]
    linarith
  -- the level sets of the shrinking cones
  let Mfun : ℝ → ℝ := fun t => Real.exp (2 * C * t) * (K₀ + t * (F + η))
  have hMfun : ∀ t : ℝ, Mfun t = Real.exp (2 * C * t) * (K₀ + t * (F + η)) := fun t => rfl
  let Z : ℕ → Set ℝ := fun k => {x : ℝ | ∃ s₁ ψ₁ : ℝ,
      |s₁ - s₀| ≤ A * (τ₀ - (k : ℝ) * h) ∧ |ψ₁ - ψ₀| ≤ A * (τ₀ - (k : ℝ) * h) ∧
      x = (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
            (fun i : Fin n => |φ i s₁ ψ₁ ((k : ℝ) * h)|)}
  have ht_le : ∀ k : ℕ, k ≤ N → (k : ℝ) * h ≤ τ₀ := by
    intro k hk
    calc (k : ℝ) * h ≤ (N : ℝ) * h :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hhpos.le
      _ = τ₀ := hNh
  have hZne : ∀ k : ℕ, k ≤ N → (Z k).Nonempty := by
    intro k hk
    refine ⟨_, s₀, ψ₀, ?_, ?_, rfl⟩
    · rw [sub_self, abs_zero]
      exact mul_nonneg hA (by linarith [ht_le k hk])
    · rw [sub_self, abs_zero]
      exact mul_nonneg hA (by linarith [ht_le k hk])
  -- the induction on the level index
  have hkey : ∀ k : ℕ, k ≤ N → BddAbove (Z k) ∧ sSup (Z k) ≤ Mfun ((k : ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hbk : ∀ x ∈ Z 0, x ≤ K₀ := by
        intro x hx
        obtain ⟨s₁, ψ₁, -, -, rfl⟩ := hx
        refine Finset.sup'_le Finset.univ_nonempty _ (fun i _ => ?_)
        simpa using h0 i s₁ ψ₁
      refine ⟨⟨K₀, hbk⟩, ?_⟩
      have hcs := csSup_le (hZne 0 (Nat.zero_le _)) hbk
      simpa [hMfun] using hcs
    | succ k ih =>
      intro hk1
      have hk : k ≤ N := le_trans (Nat.le_succ k) hk1
      obtain ⟨hbk, hsupk⟩ := ih hk
      have hk1_le : ((k + 1 : ℕ) : ℝ) * h ≤ τ₀ := ht_le (k + 1) hk1
      have hkh_le : (k : ℝ) * h ≤ τ₀ - h := by linarith [ht_eq k]
      have hkhT : (k : ℝ) * h < T := by linarith [hτ₀.2, hhpos]
      have hk1T : ((k + 1 : ℕ) : ℝ) * h ≤ T := by linarith [hτ₀.2]
      have hk1nn : 0 ≤ ((k + 1 : ℕ) : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hhpos.le
      have hb : ∀ x ∈ Z (k + 1), x ≤ Mfun (((k + 1 : ℕ) : ℝ) * h) := by
        intro x hx
        obtain ⟨s₁, ψ₁, hc1, hc2, rfl⟩ := hx
        set x : ℝ := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
            (fun i : Fin n => |φ i s₁ ψ₁ (((k + 1 : ℕ) : ℝ) * h)|) with hxdef
        have hs1 : |s₁| ≤ Rb := by
          have h1 : |s₁| ≤ |s₁ - s₀| + |s₀| := by
            calc |s₁| = |(s₁ - s₀) + s₀| := by rw [sub_add_cancel]
              _ ≤ |s₁ - s₀| + |s₀| := abs_add_le _ _
          have h2 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) ≤ A * τ₀ :=
            mul_le_mul_of_nonneg_left (by linarith) hA
          rw [hRbdef]
          nlinarith [h1, hc1, h2, abs_nonneg ψ₀]
        have hw1 : |ψ₁| ≤ Rb := by
          have h1 : |ψ₁| ≤ |ψ₁ - ψ₀| + |ψ₀| := by
            calc |ψ₁| = |(ψ₁ - ψ₀) + ψ₀| := by rw [sub_add_cancel]
              _ ≤ |ψ₁ - ψ₀| + |ψ₀| := abs_add_le _ _
          have h2 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) ≤ A * τ₀ :=
            mul_le_mul_of_nonneg_left (by linarith) hA
          rw [hRbdef]
          nlinarith [h1, hc2, h2, abs_nonneg s₀]
        obtain ⟨s', ψ', hs', hw', himp⟩ :=
          hstep₁ ((k : ℝ) * h) ⟨mul_nonneg (Nat.cast_nonneg k) hhpos.le, hkhT⟩ h hhpos
            hh_lt (by rw [← ht_eq k]; exact hk1T) s₁ ψ₁ hs1 hw1
        have hcone_s : |s' - s₀| ≤ A * (τ₀ - (k : ℝ) * h) := by
          have h1 : |s' - s₀| ≤ |s' - s₁| + |s₁ - s₀| := by
            rw [show s' - s₀ = (s' - s₁) + (s₁ - s₀) by ring]
            exact abs_add_le _ _
          have h3 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) + A * h = A * (τ₀ - (k : ℝ) * h) := by
            rw [ht_eq k]; ring
          linarith [h1, hs', hc1, h3]
        have hcone_w : |ψ' - ψ₀| ≤ A * (τ₀ - (k : ℝ) * h) := by
          have h1 : |ψ' - ψ₀| ≤ |ψ' - ψ₁| + |ψ₁ - ψ₀| := by
            rw [show ψ' - ψ₀ = (ψ' - ψ₁) + (ψ₁ - ψ₀) by ring]
            exact abs_add_le _ _
          have h3 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) + A * h = A * (τ₀ - (k : ℝ) * h) := by
            rw [ht_eq k]; ring
          linarith [h1, hw', hc2, h3]
        have hM : ∀ j, |φ j s' ψ' ((k : ℝ) * h)| ≤ sSup (Z k) := by
          intro j
          refine le_trans (Finset.le_sup'
            (fun i : Fin n => |φ i s' ψ' ((k : ℝ) * h)|) (Finset.mem_univ j))
            (le_csSup hbk ?_)
          exact ⟨s', ψ', hcone_s, hcone_w, rfl⟩
        have hB : ∀ j, |φ j s₁ ψ₁ ((k : ℝ) * h + h)| ≤ x := by
          intro j
          rw [← ht_eq k]
          exact Finset.le_sup' (fun i : Fin n => |φ i s₁ ψ₁ (((k + 1 : ℕ) : ℝ) * h)|)
            (Finset.mem_univ j)
        have hconcl := himp (sSup (Z k)) x hM hB
        have hxle : x ≤ sSup (Z k) + h * (C * x + F) + η * h := by
          refine Finset.sup'_le Finset.univ_nonempty _ (fun j _ => ?_)
          rw [ht_eq k]
          exact hconcl j
        have hxle' : x ≤ Real.exp (2 * C * ((k : ℝ) * h)) * (K₀ + ((k : ℝ) * h) * (F + η))
            + h * (F + η) + h * C * x := by
          have h3 : Mfun ((k : ℝ) * h) =
              Real.exp (2 * C * ((k : ℝ) * h)) * (K₀ + ((k : ℝ) * h) * (F + η)) := hMfun _
          have h2 : h * (C * x + F) + η * h = h * (F + η) + h * C * x := by ring
          linarith [hxle, hsupk, h3]
        have hfin := key_step hK₀ hFη hC (mul_nonneg (Nat.cast_nonneg k) hhpos.le) hhpos.le
          hCh hxle'
        rw [ht_eq k]
        simpa [hMfun] using hfin
      refine ⟨⟨Mfun (((k + 1 : ℕ) : ℝ) * h), hb⟩, ?_⟩
      exact csSup_le (hZne (k + 1) hk1) hb
  -- evaluate at the last level
  obtain ⟨hbN, hsupN⟩ := hkey N le_rfl
  have hNh0 : τ₀ - (N : ℝ) * h = 0 := by rw [hNh]; ring
  have hmemN : (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
      (fun i : Fin n => |φ i s₀ ψ₀ τ₀|) ∈ Z N := by
    refine ⟨s₀, ψ₀, ?_, ?_, ?_⟩
    · rw [sub_self, abs_zero, hNh0, mul_zero]
    · rw [sub_self, abs_zero, hNh0, mul_zero]
    · rw [hNh]
  calc |φ k₀ s₀ ψ₀ τ₀|
      ≤ (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
          (fun i : Fin n => |φ i s₀ ψ₀ τ₀|) :=
        Finset.le_sup' (fun i : Fin n => |φ i s₀ ψ₀ τ₀|) (Finset.mem_univ k₀)
    _ ≤ sSup (Z N) := le_csSup hbN hmemN
    _ ≤ Mfun ((N : ℝ) * h) := hsupN
    _ = Real.exp (2 * C * τ₀) * (K₀ + τ₀ * (F + η)) := by rw [hNh]


end Work.FTS.RegExportIface.RXT
