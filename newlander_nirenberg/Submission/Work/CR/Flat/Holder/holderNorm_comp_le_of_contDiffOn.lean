import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le

noncomputable section

set_option maxHeartbeats 4000000

universe u v

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

/-- The operator norm on the space of bilinear continuous maps whose arguments live in spaces
of continuous linear maps.  This is the canonical instance; we register it as a `local
instance` because instance search does not reach it through the deep nesting of
`ContinuousLinearMap` structures (same device as in `holderNorm_comp_le`). -/
private def normNestedCLMn (X Y A : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup A] [NormedSpace ℝ A] :
    Norm ((Y →L[ℝ] A) →L[ℝ] (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] A)) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := Y →L[ℝ] A) (F := (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] A))

attribute [local instance] normNestedCLMn

/-- Composition estimate in the combined norms `TN`, for targets in an arbitrary normed
space, with the differentiability hypothesis on `u` weakened to `C^k`: for every order `k`
there is a constant `c ≥ 0` such that the `TN k`-norm of `u ∘ Φ` on `s` is bounded by `c`
times the `TN k`-norm of `u` on `t`, for every `u` which is only `C^k` on `t`.

This is the same induction as `comp_bound_aux_local`; only the `C^∞` hypothesis on `u` is
replaced by `ContDiffOn ℝ k u t`, which is all the argument ever uses (through
`ContDiffOn.fderivWithin`, `ContDiffOn.of_le` and the induction hypothesis). -/
theorem comp_bound_aux_contDiffOn_local {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X} {t : Set Y}
    (hst : Set.MapsTo Φ s t) (hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ s)
    (hs : IsOpen s) (ht : IsOpen t) (L : ℝ)
    (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) (α : ℝ) (hα : 0 < α)
    (D : ℕ → ℝ) (hD : ∀ (k : ℕ) (x : X), x ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k)
    (E : ℕ → ℝ)
    (hE : ∀ (k : ℕ) (x : X), x ∈ s → ∀ (y : X), y ∈ s →
      ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) :
    ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (A : Type u) [NormedAddCommGroup A] [NormedSpace ℝ A]
      (u : Y → A), ContDiffOn ℝ (k : WithTop ENat) u t →
      TN k α (u ∘ Φ) s ≤ ENNReal.ofReal c * TN k α u t := by
  intro k
  induction k with
  | zero =>
    refine ⟨1 + (max L 0) ^ α, ?_, ?_⟩
    · have h := Real.rpow_nonneg (le_max_right L 0) α
      linarith
    · intro A _ _ u _
      refine TN_zero_comp_le hα (le_max_right L 0) hst ?_ u
      intro x hx y hy
      have h2 : L * ‖x - y‖ ≤ max L 0 * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (le_max_left L 0) (norm_nonneg _)
      linarith [hL x hx y hy]
  | succ k ih =>
    obtain ⟨c, hc0, ihc⟩ := ih
    set DB : ℝ := (∑ m ∈ Finset.range (k + 2), |D m|) + 1 with hDB
    set EB : ℝ := (∑ m ∈ Finset.range (k + 2), |E m|) + 1 with hEB
    have hDBpos : 0 < DB := by rw [hDB]; positivity
    have hEBpos : 0 < EB := by rw [hEB]; positivity
    have hDBle : ∀ m ≤ k + 1, max (D m) 0 ≤ DB := by
      intro m hm
      have h1 : |D m| ≤ ∑ i ∈ Finset.range (k + 2), |D i| :=
        Finset.single_le_sum (f := fun i => |D i|) (fun i _ => abs_nonneg _) (a := m)
          (Finset.mem_range.mpr (by omega))
      have h2 : D m ≤ |D m| := le_abs_self _
      have h3 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 2), |D i| :=
        Finset.sum_nonneg (fun i _ => abs_nonneg _)
      rw [hDB]
      exact max_le (by linarith) (by linarith)
    have hEBle : ∀ m ≤ k + 1, max (E m) 0 ≤ EB := by
      intro m hm
      have h1 : |E m| ≤ ∑ i ∈ Finset.range (k + 2), |E i| :=
        Finset.single_le_sum (f := fun i => |E i|) (fun i _ => abs_nonneg _) (a := m)
          (Finset.mem_range.mpr (by omega))
      have h2 : E m ≤ |E m| := le_abs_self _
      have h3 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 2), |E i| :=
        Finset.sum_nonneg (fun i _ => abs_nonneg _)
      rw [hEB]
      exact max_le (by linarith) (by linarith)
    set d1 : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (c * DB) with hd1
    set d2 : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (c * (DB + EB)) with hd2
    have hd1nn : 0 ≤ d1 := by
      rw [hd1]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 hDBpos.le)
    have hd2nn : 0 ≤ d2 := by
      rw [hd2]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 (add_nonneg hDBpos.le hEBpos.le))
    refine ⟨c + d1 + d2, by linarith, ?_⟩
    intro A _ _ u hu
    set v : Y → (Y →L[ℝ] A) := fun y => fderivWithin ℝ u t y with hv
    set Ψ : X → (X →L[ℝ] Y) := fun x => fderivWithin ℝ Φ s x with hΨ
    set B : (Y →L[ℝ] A) →L[ℝ] (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] A) :=
      ContinuousLinearMap.compL ℝ X Y A with hB
    set N : ℝ≥0∞ := TN (k + 1) α u t with hN
    have hUs : UniqueDiffOn ℝ s := hs.uniqueDiffOn
    have hUt : UniqueDiffOn ℝ t := ht.uniqueDiffOn
    have hu_k : ContDiffOn ℝ (k : WithTop ENat) u t :=
      hu.of_le (by rw [Nat.cast_succ]; exact le_add_right le_rfl)
    have hu1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ENat) u t :=
      hu.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
    have hv' : ContDiffOn ℝ (k : WithTop ENat) v t :=
      hu.fderivWithin hUt (by rw [Nat.cast_succ])
    have hIH : TN k α (v ∘ Φ) s ≤ ENNReal.ofReal c * TN k α v t :=
      ihc (Y →L[ℝ] A) v hv'
    have hvC : TN k α (v ∘ Φ) s ≤ ENNReal.ofReal c * N := by
      have h := hIH.trans
        (mul_le_mul_right (TN_fderivWithin_le k α u t hUt) (ENNReal.ofReal c))
      simpa only [hN] using h
    have hΦDN : ∀ m ≤ k + 1, iDN m Φ s ≤ ENNReal.ofReal DB := by
      intro m hm
      exact (iDN_le_ofReal_max Φ D s m (fun x hx => hD m x hx)).trans
        (ENNReal.ofReal_le_ofReal (hDBle m hm))
    have hΦSN : ∀ m ≤ k + 1, hSN m α Φ s ≤ ENNReal.ofReal EB := by
      intro m hm
      exact (hSN_le_ofReal_max Φ E s m α (fun x hx y hy => hE m x hx y hy)).trans
        (ENNReal.ofReal_le_ofReal (hEBle m hm))
    have hΨDN : ∀ m ≤ k, iDN m Ψ s ≤ ENNReal.ofReal DB := by
      intro m hm
      have h : iDN m Ψ s = iDN (m + 1) Φ s := by
        rw [hΨ, iDN_fderivWithin m Φ s hUs]
      rw [h]
      exact hΦDN (m + 1) (by omega)
    have hΨSN : ∀ m ≤ k, hSN m α Ψ s ≤ ENNReal.ofReal EB := by
      intro m hm
      have h : hSN m α Ψ s = hSN (m + 1) α Φ s := by
        rw [hΨ, hSN_fderivWithin m α Φ s hUs]
      rw [h]
      exact hΦSN (m + 1) (by omega)
    have hvΦDN : ∀ j ≤ k, iDN j (v ∘ Φ) s ≤ ENNReal.ofReal c * N := fun j hj =>
      (iDN_le_TN k j α hj).trans hvC
    have hvΦSN : ∀ j ≤ k, hSN j α (v ∘ Φ) s ≤ ENNReal.ofReal c * N := fun j hj =>
      (hSN_le_TN k j α hj).trans hvC
    have hchain : ∀ x ∈ s, fderivWithin ℝ (u ∘ Φ) s x = B ((v ∘ Φ) x) (Ψ x) := by
      intro x hx
      have h := fderivWithin_comp_eq hs ht hst
        ((hΦ 1).differentiableOn (by positivity)) (hu1.differentiableOn (by positivity)) x hx
      rw [hB]
      exact h
    have hvΦc : ContDiffOn ℝ k (v ∘ Φ) s := ContDiffOn.comp hv' (hΦ k) hst
    have hΨc : ContDiffOn ℝ k Ψ s := by
      rw [hΨ]
      exact (hΦ (k + 1)).fderivWithin hUs (by simp only [Nat.cast_succ, le_refl])
    have hBnorm : ENNReal.ofReal ‖B‖ ≤ 1 := by
      rw [hB, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      change sInf {c : ℝ | 0 ≤ c ∧ ∀ x,
        ‖(ContinuousLinearMap.compL ℝ X Y A) x‖ ≤ c * ‖x‖} ≤ 1
      refine csInf_le ⟨0, fun c hc => hc.1⟩ ⟨zero_le_one, fun x => ?_⟩
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
        (E := X →L[ℝ] Y) (F := X →L[ℝ] A) _ (norm_nonneg x) fun g => ?_
      exact ContinuousLinearMap.opNorm_comp_le x g
    have hS1 : (∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s))
        ≤ ENNReal.ofReal d1 * N := by
      rw [hd1, ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 hDBpos.le)), Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s)
          ≤ (k.choose j : ℝ≥0∞) * ((ENNReal.ofReal c * N) * ENNReal.ofReal DB) :=
            mul_le_mul_right (mul_le_mul' (hvΦDN j hjk) (hΨDN (k - j) (by omega))) _
        _ = ENNReal.ofReal ((k.choose j : ℝ) * (c * DB)) * N := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg (k.choose j)), ENNReal.ofReal_mul hc0,
              ENNReal.ofReal_natCast]
            ring
    have hS2 : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
          (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s))
        ≤ ENNReal.ofReal d2 * N := by
      rw [hd2, ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg hc0 (add_nonneg hDBpos.le hEBpos.le))), Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 : hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
          ≤ (ENNReal.ofReal c * N) * ENNReal.ofReal DB :=
        mul_le_mul' (hvΦSN j hjk) (hΨDN (k - j) (by omega))
      have h2 : iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s
          ≤ (ENNReal.ofReal c * N) * ENNReal.ofReal EB :=
        mul_le_mul' (hvΦDN j hjk) (hΨSN (k - j) (by omega))
      calc (k.choose j : ℝ≥0∞) * (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
              + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s)
          ≤ (k.choose j : ℝ≥0∞) * ((ENNReal.ofReal c * N) * ENNReal.ofReal DB
              + (ENNReal.ofReal c * N) * ENNReal.ofReal EB) :=
            mul_le_mul_right (add_le_add h1 h2) _
        _ = ENNReal.ofReal ((k.choose j : ℝ) * (c * (DB + EB))) * N := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg (k.choose j)), ENNReal.ofReal_mul hc0,
              ENNReal.ofReal_add hDBpos.le hEBpos.le, ENNReal.ofReal_natCast]
            ring
    have hDNtop : iDN (k + 1) (u ∘ Φ) s ≤ ENNReal.ofReal d1 * N := by
      have h1 : iDN (k + 1) (u ∘ Φ) s
          = iDN k (fun x => fderivWithin ℝ (u ∘ Φ) s x) s :=
        (iDN_fderivWithin k (u ∘ Φ) s hUs).symm
      have h2 : iDN k (fun x => fderivWithin ℝ (u ∘ Φ) s x) s
          = iDN k (fun x => B ((v ∘ Φ) x) (Ψ x)) s :=
        iDN_congr fun x hx => hchain x hx
      rw [h1, h2]
      have h3 := iDN_bilinear_le (B := B) k (f := v ∘ Φ) (g := Ψ) (Ω := s) hvΦc hΨc hUs
      calc iDN k (fun x => B ((v ∘ Φ) x) (Ψ x)) s
          ≤ ENNReal.ofReal ‖B‖ * (∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s)) := h3
        _ ≤ 1 * (∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s)) :=
            mul_le_mul_left hBnorm _
        _ = ∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s) := one_mul _
        _ ≤ ENNReal.ofReal d1 * N := hS1
    have hSNtop : hSN (k + 1) α (u ∘ Φ) s ≤ ENNReal.ofReal d2 * N := by
      have h1 : hSN (k + 1) α (u ∘ Φ) s
          = hSN k α (fun x => fderivWithin ℝ (u ∘ Φ) s x) s :=
        (hSN_fderivWithin k α (u ∘ Φ) s hUs).symm
      have h2 : hSN k α (fun x => fderivWithin ℝ (u ∘ Φ) s x) s
          = hSN k α (fun x => B ((v ∘ Φ) x) (Ψ x)) s :=
        hSN_congr fun x hx => hchain x hx
      rw [h1, h2]
      have h3 := hSN_bilinear_le k α B (f := v ∘ Φ) (g := Ψ) (Ω := s) hvΦc hΨc hUs
      calc hSN k α (fun x => B ((v ∘ Φ) x) (Ψ x)) s
          ≤ ENNReal.ofReal ‖B‖ * (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
              (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
                + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s)) := h3
        _ ≤ 1 * (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
              (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
                + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s)) :=
            mul_le_mul_left hBnorm _
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
              (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
                + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s) := one_mul _
        _ ≤ ENNReal.ofReal d2 * N := hS2
    have hbase : TN k α (u ∘ Φ) s ≤ ENNReal.ofReal c * N := by
      have h := (ihc A u hu_k).trans (mul_le_mul_right (TN_mono k α u t) (ENNReal.ofReal c))
      simpa only [hN] using h
    have hsum : ENNReal.ofReal (c + d1 + d2) * N
        = ENNReal.ofReal c * N + (ENNReal.ofReal d1 * N + ENNReal.ofReal d2 * N) := by
      have h1 : ENNReal.ofReal (c + d1 + d2)
          = ENNReal.ofReal c + ENNReal.ofReal d1 + ENNReal.ofReal d2 := by
        rw [ENNReal.ofReal_add (add_nonneg hc0 hd1nn) hd2nn,
          ENNReal.ofReal_add hc0 hd1nn]
      rw [h1, add_mul, add_mul, add_assoc]
    rw [TN_succ]
    exact (add_le_add hbase (add_le_add hDNtop hSNtop)).trans (le_of_eq hsum.symm)

/-- The composition estimate for the Hölder norms, with the two universes of `X` and `Y`
kept independent and with the differentiability hypothesis on `u` weakened to `C^k`: proved
by lifting both `X` and `Y` into a common universe and applying
`comp_bound_aux_contDiffOn_local`. -/
theorem holderNorm_comp_le_general_contDiffOn {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y}
    {s : Set X} {t : Set Y}
    (hst : Set.MapsTo Φ s t) (hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ s)
    (hs : IsOpen s) (ht : IsOpen t) (L : ℝ)
    (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) (α : ℝ) (hα : 0 < α)
    (D : ℕ → ℝ) (hD : ∀ (k : ℕ) (x : X), x ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k)
    (E : ℕ → ℝ)
    (hE : ∀ (k : ℕ) (x : X), x ∈ s → ∀ (y : X), y ∈ s →
      ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (u : Y → ℂ),
      ContDiffOn ℝ (k : WithTop ENat) u t →
      Work.CR.Flat.holderNorm k α (u ∘ Φ) s ≤ ENNReal.ofReal (C k) * holderNorm k α u t := by
  let eX : ULift.{max u v} X ≃ₗᵢ[ℝ] X := uliftLIE X
  let eY : ULift.{max u v} Y ≃ₗᵢ[ℝ] Y := uliftLIE Y
  let eC : ULift.{max u v} ℂ ≃ₗᵢ[ℝ] ℂ := uliftLIE ℂ
  let Φ' : ULift.{max u v} X → ULift.{max u v} Y := fun x => eY.symm (Φ (eX x))
  have hs' : IsOpen (eX ⁻¹' s) := hs.preimage eX.continuous
  have ht' : IsOpen (eY ⁻¹' t) := ht.preimage eY.continuous
  have hUs : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hUt : UniqueDiffOn ℝ t := ht.uniqueDiffOn
  have hUs' : UniqueDiffOn ℝ (eX ⁻¹' s) := hs'.uniqueDiffOn
  have hUt' : UniqueDiffOn ℝ (eY ⁻¹' t) := ht'.uniqueDiffOn
  have hst' : Set.MapsTo Φ' (eX ⁻¹' s) (eY ⁻¹' t) := by
    intro x hx
    show eY (Φ' x) ∈ t
    rw [show Φ' x = eY.symm (Φ (eX x)) from rfl, eY.apply_symm_apply]
    exact hst hx
  have hΦ' : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ' (eX ⁻¹' s) := by
    intro m
    have h1 : ContDiffOn ℝ (m : WithTop ENat) (fun x : ULift.{max u v} X => Φ (eX x))
        (eX ⁻¹' s) :=
      ContDiffOn.comp_continuousLinearMap (hΦ m) (eX : ULift.{max u v} X →L[ℝ] X)
    exact ContDiffOn.comp ((LinearIsometryEquiv.contDiff eY.symm).contDiffOn) h1
      (Set.mapsTo_univ _ _)
  have hL' : ∀ x ∈ eX ⁻¹' s, ∀ y ∈ eX ⁻¹' s, ‖Φ' x - Φ' y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    have h1 : ‖Φ' x - Φ' y‖ = ‖Φ (eX x) - Φ (eX y)‖ := by
      rw [show Φ' x - Φ' y = eY.symm (Φ (eX x) - Φ (eX y)) by
            simp only [Φ', map_sub],
        LinearIsometryEquiv.norm_map]
    have h2 : ‖x - y‖ = ‖eX x - eX y‖ := by
      rw [← eX.norm_map (x - y), map_sub]
    rw [h1, h2]
    exact hL (eX x) hx (eX y) hy
  have hD' : ∀ (k : ℕ) (x : ULift.{max u v} X), x ∈ eX ⁻¹' s →
      ‖iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) x‖ ≤ D k := by
    intro k x hx
    change ‖iteratedFDerivWithin ℝ k (fun x' => eY.symm (Φ (eX x'))) (eX ⁻¹' s) x‖ ≤ D k
    have hleft : ‖iteratedFDerivWithin ℝ k (fun x' => eY.symm (Φ (eX x'))) (eX ⁻¹' s) x‖
        = ‖iteratedFDerivWithin ℝ k (fun x' => Φ (eX x')) (eX ⁻¹' s) x‖ :=
      LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left eY.symm
        (f := fun x' : ULift.{max u v} X => Φ (eX x')) hUs' hx k
    have hright : ‖iteratedFDerivWithin ℝ k (fun x' => Φ (eX x')) (eX ⁻¹' s) x‖
        = ‖iteratedFDerivWithin ℝ k Φ s (eX x)‖ :=
      LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right eX Φ hUs hx k
    rw [hleft, hright]
    exact hD k (eX x) hx
  have hE' : ∀ (k : ℕ) (x : ULift.{max u v} X), x ∈ eX ⁻¹' s →
      ∀ (y : ULift.{max u v} X), y ∈ eX ⁻¹' s →
      ‖iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) x
        - iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) y‖ ≤ E k * ‖x - y‖ ^ α := by
    intro k x hx y hy
    have h1 : ‖iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) x
        - iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) y‖
        = ‖iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x')) (eX ⁻¹' s) x
            - iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x'))
                (eX ⁻¹' s) y‖ :=
      norm_iteratedFDerivWithin_sub_comp_lie_left eY.symm
        (fun x' : ULift.{max u v} X => Φ (eX x')) k (eX ⁻¹' s) hUs' hx hy
    have h2 : ‖iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x')) (eX ⁻¹' s) x
        - iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x')) (eX ⁻¹' s) y‖
        = ‖iteratedFDerivWithin ℝ k Φ s (eX x) - iteratedFDerivWithin ℝ k Φ s (eX y)‖ :=
      norm_iteratedFDerivWithin_sub_comp_lie_right eX Φ k s hUs hx hy
    have h3 : ‖x - y‖ = ‖eX x - eX y‖ := by
      rw [← eX.norm_map (x - y), map_sub]
    rw [h1, h2, h3]
    exact hE k (eX x) hx (eX y) hy
  choose C hC using comp_bound_aux_contDiffOn_local hst' hΦ' hs' ht' L hL' α hα D hD' E hE'
  refine ⟨fun k => C k + 1, fun k => by
      have := (hC k).1
      linarith, fun k u hu => ?_⟩
  have hu' : ContDiffOn ℝ (k : WithTop ENat)
      (fun y : ULift.{max u v} Y => eC.symm (u (eY y))) (eY ⁻¹' t) := by
    have h1 : ContDiffOn ℝ (k : WithTop ENat) (fun y : ULift.{max u v} Y => u (eY y))
        (eY ⁻¹' t) :=
      ContDiffOn.comp_continuousLinearMap hu (eY : ULift.{max u v} Y →L[ℝ] Y)
    exact ContDiffOn.comp ((LinearIsometryEquiv.contDiff eC.symm).contDiffOn) h1
      (Set.mapsTo_univ _ _)
  have h := (hC k).2 (ULift.{max u v} ℂ) (fun y => eC.symm (u (eY y))) hu'
  have hcomp : (fun y => eC.symm (u (eY y))) ∘ Φ'
      = fun x => eC.symm ((u ∘ Φ) (eX x)) := by
    funext x
    show eC.symm (u (eY (eY.symm (Φ (eX x))))) = eC.symm (u (Φ (eX x)))
    rw [eY.apply_symm_apply]
  have hTN1 : TN k α ((fun y => eC.symm (u (eY y))) ∘ Φ') (eX ⁻¹' s)
      = TN k α (u ∘ Φ) s := by
    have h1 : TN k α (fun x => eC.symm ((u ∘ Φ) (eX x))) (eX ⁻¹' s)
        = TN k α (fun x => (u ∘ Φ) (eX x)) (eX ⁻¹' s) :=
      TN_comp_lie_left eC.symm (fun x => (u ∘ Φ) (eX x)) k α (eX ⁻¹' s) hUs'
    have h2 : TN k α (fun x => (u ∘ Φ) (eX x)) (eX ⁻¹' s) = TN k α (u ∘ Φ) s :=
      TN_comp_lie_right eX (u ∘ Φ) k α s hUs
    rw [hcomp, h1, h2]
  have hTN2 : TN k α (fun y => eC.symm (u (eY y))) (eY ⁻¹' t) = TN k α u t := by
    have h1 : TN k α (fun y => eC.symm (u (eY y))) (eY ⁻¹' t)
        = TN k α (fun y => u (eY y)) (eY ⁻¹' t) :=
      TN_comp_lie_left eC.symm (fun y => u (eY y)) k α (eY ⁻¹' t) hUt'
    have h2 : TN k α (fun y => u (eY y)) (eY ⁻¹' t) = TN k α u t :=
      TN_comp_lie_right eY u k α t hUt
    rw [h1, h2]
  rw [hTN1, hTN2] at h
  have e1 : holderNorm k α (u ∘ Φ) s = TN k α (u ∘ Φ) s := by
    simp only [holderNorm, TN, iDN_complex_eq, hSN_complex_eq]
  have e2 : holderNorm k α u t = TN k α u t := by
    simp only [holderNorm, TN, iDN_complex_eq, hSN_complex_eq]
  rw [e1, e2]
  exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _)

end Work.CR.Flat.Holder

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal

/-- **Composition of Hölder norms**, in the `C^k` (rather than `C^∞`) formulation: if `Φ`
maps an open set `s` into an open set `t`, is `C^∞` with derivative bounds `D`, `E` and
Lipschitz constant `L` on `s`, and `α > 0`, then for every order `k` there is a positive
constant `C k` such that for every `u : Y → ℂ` which is only `C^k` on `t`,
`holderNorm k α (u ∘ Φ) s ≤ C k * holderNorm k α u t`. -/
theorem holderNorm_comp_le_of_contDiffOn {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X}
    {t : Set Y}
    (hst : Set.MapsTo Φ s t) (hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ s) (hs : IsOpen s)
    (ht : IsOpen t) (L : ℝ) (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖)
    (α : ℝ) (hα : 0 < α) (D : ℕ → ℝ) (hD : ∀ (k : ℕ) (x : X), x ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k)
    (E : ℕ → ℝ) (hE : ∀ (k : ℕ) (x : X), x ∈ s → ∀ (y : X), y ∈ s →
      ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (u : Y → ℂ),
      ContDiffOn ℝ (k : WithTop ENat) u t →
      Work.CR.Flat.holderNorm k α (u ∘ Φ) s ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α u t :=
  holderNorm_comp_le_general_contDiffOn hst hΦ hs ht L hL α hα D hD E hE

end Work.CR.Flat.Holder
