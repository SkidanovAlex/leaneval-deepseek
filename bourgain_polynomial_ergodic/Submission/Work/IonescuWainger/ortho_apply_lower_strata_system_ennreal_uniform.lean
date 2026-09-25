import Mathlib
import Submission.Work.IonescuWainger.ortho_apply_lower_strata_system
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_sum_singletons
import Submission.Work.BourgainPlan.IonescuWainger.sigmaStrataFinset_union_add
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2_endpoint_strata
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs

/-!
# The lower bound of Tao's `ortho-apply`(i) in `ℝ≥0∞`, with a constant uniform in `S`

This is the `ℝ≥0∞`-valued form of `Work.IonescuWainger.ortho_apply_lower_strata_system` (itself Tao's
`ortho-apply`(i), arXiv:2008.05066 §4, for the concrete major-arc system
`δ ↦ Op_{ψ;{δ}} f`), with the extra requirement that the constant `C` depends only on `k` and `r`:
not on the pairwise coprime set `S`, nor on `M`, `ε`, `ψ`, the coefficients `εs`, or `f`.

Two things have to be added to the real-valued form:

* the band-limitation hypothesis `HasFreqSupport (opArc ψ hψ {δ} f hf) (arcSet δ ε)` is not an
  assumption here but a *consequence* of `ψ` vanishing off the `ε`-ball
  (`hasFreqSupport_opArc` applied to `D = {‖·‖ ≤ ε}` and the elementary circle fact that a point at
  distance `≤ ε` of `δ` lies in `arcSet δ ε`);
* the passage from the real `tsum` inequality to the `ℝ≥0∞` inequality needs *summability* of the
  two series involved (`ENNReal.ofReal_tsum_of_nonneg`).  Summability is not free: it is proved
  from the pointwise domination of the strata sums by the single-frequency square function
  `x ↦ Σ_{β ∈ B} ‖opArc ψ hψ {β} f hf x‖²` (which is summable because `f ∈ ℓ²` and the single
  frequency multipliers are `ℓ²`-bounded), first for the left-hand side and then for each of the
  shifted square functions on the right.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.IonescuWainger

open Work.BourgainPlan.IonescuWainger

/-! ## Elementary helpers -/

/-- A point of the circle whose distance from `δ` is at most `ε` lies in the arc `arcSet δ ε`. -/
private theorem mem_arcSet_of_norm_sub_le {δ ξ : Work.BourgainPlan.IonescuWainger.Circle} {ε : ℝ} (h : ‖ξ - δ‖ ≤ ε) :
    ξ ∈ arcSet δ ε := by
  rw [arcSet]
  obtain ⟨y, -, hy⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) (ξ - δ)
  have hz0 : ((↑(round y : ℤ) : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) = 0 := by
    have h1 := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := (round y : ℤ)) (x := (1 : ℝ))
    rw [AddCircle.coe_period (p := (1 : ℝ))] at h1
    simpa [zsmul_eq_mul] using h1
  have hy' : (y : Work.BourgainPlan.IonescuWainger.Circle) = ξ - δ := hy
  refine ⟨y - ↑(round y : ℤ), ?_, ?_⟩
  · have hnorm : ‖(y : Work.BourgainPlan.IonescuWainger.Circle)‖ = |y - ↑(round y : ℤ)| := by
      have h2 := AddCircle.norm_eq (1 : ℝ) (x := y)
      simpa using h2
    rw [← hnorm, hy']
    exact h
  · rw [show ((y - ↑(round y : ℤ) : ℝ) : Work.BourgainPlan.IonescuWainger.Circle)
        = (y : Work.BourgainPlan.IonescuWainger.Circle) - ((↑(round y : ℤ) : ℝ) : Work.BourgainPlan.IonescuWainger.Circle)
        from AddCircle.coe_sub (1 : ℝ) y (↑(round y : ℤ))]
    rw [hz0, sub_zero, hy']
    show ξ = δ + (ξ - δ)
    abel

/-- A finite square function of a family of `ℓ²` sequences is summable. -/
private theorem summable_finset_sq_norm {B : Finset Work.BourgainPlan.IonescuWainger.Circle} {g : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ}
    (hg : ∀ β, Memℓp (g β) 2) :
    Summable fun x : ℤ => ∑ β ∈ B, ‖g β x‖ ^ 2 := by
  refine summable_sum (L := SummationFilter.unconditional ℤ) (f := fun β x => ‖g β x‖ ^ 2)
    (s := B) fun β _ => ?_
  exact summable_norm_sq_of_memℓp (hg β)

/-- If `T` is nonnegative and dominated pointwise by `N` times a summable nonnegative `W`, then
the `r`-th powers of `T` are summable (`r ≥ 1`).  This is the standard `ℓ^p`-layer-cake step used
to turn the `ℓ²` summability of the single-frequency square function into summability of the
`(2r)`-th power series. -/
private theorem summable_pow_of_le_mul {T W : ℤ → ℝ} {N : ℝ} (hN : 0 ≤ N) (hW : Summable W)
    (hWnn : ∀ x, 0 ≤ W x) (hTnn : ∀ x, 0 ≤ T x) (hle : ∀ x, T x ≤ N * W x)
    {r : ℕ} (hr : 1 ≤ r) : Summable fun x : ℤ => T x ^ r := by
  set M : ℝ := max 1 (∑' x, W x) with hMdef
  have hWle : ∀ x, W x ≤ M := fun x =>
    le_trans (hW.le_tsum x (fun j _ => hWnn j)) (le_max_right _ _)
  have hMnn : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hTle : ∀ x, T x ≤ N * M := fun x =>
    le_trans (hle x) (mul_le_mul_of_nonneg_left (hWle x) hN)
  refine Summable.of_nonneg_of_le (fun x => pow_nonneg (hTnn x) r) (fun x => ?_)
    (hW.mul_left ((N * M) ^ (r - 1) * N))
  have h1 : T x ^ r = T x ^ (r - 1) * T x := by
    conv_lhs => rw [show r = (r - 1) + 1 from (Nat.sub_add_cancel hr).symm]
    rw [pow_succ]
  rw [h1]
  have h2 : T x ^ (r - 1) ≤ (N * M) ^ (r - 1) := pow_le_pow_left₀ (hTnn x) (hTle x) _
  calc T x ^ (r - 1) * T x ≤ (N * M) ^ (r - 1) * (N * W x) :=
        mul_le_mul h2 (hle x) (hTnn x) (by positivity)
    _ = ((N * M) ^ (r - 1) * N) * W x := by ring

/-- The pointwise bound for a coefficient-weighted sum of strata sums: a sum of `Σ_{E ∈ P}` of
`c E · (Σ_{β ∈ γ E} g β x)`, with `‖c E‖ ≤ 1` and every `γ E ⊆ B`, is bounded by
`(P.card)² · (B.card) · Σ_{β ∈ B} ‖g β x‖²`. -/
private theorem norm_sum_strata_sq_le {ι : Type*} {P : Finset ι} {c : ι → ℂ}
    (hc : ∀ E, ‖c E‖ ≤ 1) {B : Finset Work.BourgainPlan.IonescuWainger.Circle} {γ : ι → Finset Work.BourgainPlan.IonescuWainger.Circle}
    (hsub : ∀ E ∈ P, γ E ⊆ B) {g : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ} (x : ℤ) :
    ‖∑ E ∈ P, c E * (∑ β ∈ γ E, g β x)‖ ^ 2
      ≤ (P.card : ℝ) ^ 2 * (B.card : ℝ) * (∑ β ∈ B, ‖g β x‖ ^ 2) := by
  have h1 : ‖∑ E ∈ P, c E * (∑ β ∈ γ E, g β x)‖ ≤ ∑ E ∈ P, ∑ β ∈ γ E, ‖g β x‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun E hE => ?_))
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc E)).trans (norm_sum_le _ _)
  have h2 : (∑ E ∈ P, ∑ β ∈ γ E, ‖g β x‖) ≤ (P.card : ℝ) * (∑ β ∈ B, ‖g β x‖) := by
    calc ∑ E ∈ P, ∑ β ∈ γ E, ‖g β x‖
        ≤ ∑ E ∈ P, ∑ β ∈ B, ‖g β x‖ :=
          Finset.sum_le_sum (fun E hE => Finset.sum_le_sum_of_subset_of_nonneg (hsub E hE)
            (fun i _ _ => norm_nonneg _))
      _ = (P.card : ℝ) * (∑ β ∈ B, ‖g β x‖) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc ‖∑ E ∈ P, c E * (∑ β ∈ γ E, g β x)‖ ^ 2
      ≤ ((P.card : ℝ) * (∑ β ∈ B, ‖g β x‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    _ = (P.card : ℝ) ^ 2 * (∑ β ∈ B, ‖g β x‖) ^ 2 := by ring
    _ ≤ (P.card : ℝ) ^ 2 * ((B.card : ℝ) * ∑ β ∈ B, ‖g β x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq (sq_nonneg _)
    _ = (P.card : ℝ) ^ 2 * (B.card : ℝ) * (∑ β ∈ B, ‖g β x‖ ^ 2) := by ring

/-- The pointwise bound for the shifted square function: `Σ_{α ∈ C} ‖Op_{ψ;α+E} f x‖²` is bounded
by `(E.card)² · (C.card)` times the single-frequency square function `Σ_{β ∈ B} ‖Op_{ψ;{β}} f x‖²`
over the union `B` of the shifted frequency sets. -/
private theorem sum_opArc_shift_sq_le {E C : Finset Work.BourgainPlan.IonescuWainger.Circle} {ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    (hψ : MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1))) {f : ℤ → ℂ} (hf : Memℓp f 2) (x : ℤ) :
    ∑ α ∈ C, ‖opArc ψ hψ (arcShift E α) f hf x‖ ^ 2
      ≤ (E.card : ℝ) ^ 2 * (C.card : ℝ) *
        (∑ β ∈ C.biUnion (fun α => E.image (fun γ => γ + α)), ‖opArc ψ hψ {β} f hf x‖ ^ 2) := by
  set B : Finset Work.BourgainPlan.IonescuWainger.Circle := C.biUnion (fun α => E.image (fun γ => γ + α)) with hBdef
  have hterm : ∀ α ∈ C, ‖opArc ψ hψ (arcShift E α) f hf x‖ ^ 2
      ≤ (E.card : ℝ) * (∑ γ ∈ E, ‖opArc ψ hψ {γ + α} f hf x‖ ^ 2) := by
    intro α _
    have hcongr : opArc ψ hψ (arcShift E α) f hf x = ∑ γ ∈ E, opArc ψ hψ {γ + α} f hf x := by
      rw [opArc_arcShift_eq ψ hψ E α f hf, Finset.sum_apply]
    calc ‖opArc ψ hψ (arcShift E α) f hf x‖ ^ 2
        = ‖∑ γ ∈ E, opArc ψ hψ {γ + α} f hf x‖ ^ 2 := by rw [hcongr]
      _ ≤ (∑ γ ∈ E, ‖opArc ψ hψ {γ + α} f hf x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (E.card : ℝ) * ∑ γ ∈ E, ‖opArc ψ hψ {γ + α} f hf x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  calc ∑ α ∈ C, ‖opArc ψ hψ (arcShift E α) f hf x‖ ^ 2
      ≤ ∑ α ∈ C, (E.card : ℝ) * (∑ γ ∈ E, ‖opArc ψ hψ {γ + α} f hf x‖ ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (E.card : ℝ) * ∑ α ∈ C, ∑ γ ∈ E, ‖opArc ψ hψ {γ + α} f hf x‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (E.card : ℝ) * ∑ α ∈ C, ∑ γ ∈ E, (∑ β ∈ B, ‖opArc ψ hψ {β} f hf x‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun α hα => Finset.sum_le_sum (fun γ hγ => ?_))) (by positivity)
        have hmem : γ + α ∈ B := by
          rw [hBdef]
          exact Finset.mem_biUnion.mpr ⟨α, hα, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩⟩
        exact Finset.single_le_sum (f := fun β => ‖opArc ψ hψ {β} f hf x‖ ^ 2)
          (fun β _ => sq_nonneg _) hmem
    _ = (E.card : ℝ) * ((C.card : ℝ) *
          ((E.card : ℝ) * (∑ β ∈ B, ‖opArc ψ hψ {β} f hf x‖ ^ 2))) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    _ = (E.card : ℝ) ^ 2 * (C.card : ℝ) *
          (∑ β ∈ B, ‖opArc ψ hψ {β} f hf x‖ ^ 2) := by ring

/-! ## The main theorem -/

-- Uniform-in-S form of the ENNReal lower bound; see A6_ASSEMBLY_GUIDE.md and ARC_ARITH_STATUS.md Addendum 17.
theorem ortho_apply_lower_strata_system_ennreal_uniform (k r : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {M : ℕ} (hM : 2 ≤ M)
      (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
        ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧
          Work.BourgainPlan.IonescuWainger.IsSunflower A)
      {ε : ℝ} (hε0 : 0 ≤ ε)
      (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
      (hψsupp : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ε < ‖ξ‖ → ψ ξ = 0)
      (hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) →
        Work.BourgainPlan.IonescuWainger.HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, Work.BourgainPlan.IonescuWainger.QA (A j) : ℕ) : ℝ))
      (hsmallP : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
          2 * (r : ℝ) * ε * ((Work.BourgainPlan.IonescuWainger.QA A₀ *
            (∏ i, Work.BourgainPlan.IonescuWainger.QA ((A i).1)) : ℕ) : ℝ) < 1)
      (εs : Finset ℕ → ℂ) (hεs : ∀ A, ‖εs A‖ ≤ 1) (f : ℤ → ℂ) (hf : Memℓp f 2),
      ∑' x : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          εs A * Work.BourgainPlan.IonescuWainger.opArc ψ hψ
            (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf x‖ ^ (2 * r))
        ≤ ENNReal.ofReal (C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r) *
            ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
              ∑' x : ℤ, (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
                  ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
                    (Work.BourgainPlan.IonescuWainger.arcShift
                      (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) f hf x‖ ^ 2))
                ^ (r : ℝ) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := ortho_apply_lower_strata_system k r hr hk
  refine ⟨C, hCpos, ?_⟩
  intro S h2S hS M hM hsun ε hε0 ψ hψ hψsupp hsmallN hsmallP εs hεs f hf
  -- the band-limitation of the major-arc system, from the support of `ψ`
  have hFsupp : ∀ δ : Work.BourgainPlan.IonescuWainger.Circle, HasFreqSupport (opArc ψ hψ {δ} f hf)
      (opMul_memℓp (arcSymbolLp ψ hψ {δ}) f hf) (arcSet δ ε) := by
    intro δ
    refine hasFreqSupport_mono ?_ (hasFreqSupport_opArc ψ hψ {δ} f hf (D := {η | ‖η‖ ≤ ε}) ?_)
    · rintro ξ ⟨β, hβ, hβD⟩
      rw [Finset.mem_singleton] at hβ
      subst hβ
      exact mem_arcSet_of_norm_sub_le hβD
    · intro ξ hξ
      exact hψsupp ξ (lt_of_not_ge hξ)
  have hreal := hC (S := S) h2S hS (M := M) hM hsun ψ hψ f hf hFsupp hsmallN hsmallP εs hεs
  -- the single-frequency major-arc system
  set g : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ := fun β => opArc ψ hψ {β} f hf with hgdef
  have hg : ∀ β, Memℓp (g β) 2 := fun β => opMul_memℓp (arcSymbolLp ψ hψ {β}) f hf
  set P : Finset (Finset ℕ) := S.powerset.filter (fun A => A.card ≤ k) with hPdef
  -- ### summability on the left
  set b₁ : Finset Work.BourgainPlan.IonescuWainger.Circle := P.biUnion sigmaStrataFinset with hb₁def
  set W₁ : ℤ → ℝ := fun x => ∑ β ∈ b₁, ‖g β x‖ ^ 2 with hW₁def
  have hW₁sum : Summable W₁ := by
    rw [hW₁def]
    exact summable_finset_sq_norm hg
  have hLHSle : ∀ x : ℤ,
      ‖∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x‖ ^ 2
        ≤ ((P.card : ℝ) ^ 2 * (b₁.card : ℝ)) * W₁ x := by
    intro x
    rw [hW₁def]
    have hcongr : (∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x)
        = ∑ A ∈ P, εs A * ∑ β ∈ sigmaStrataFinset A, g β x := by
      refine Finset.sum_congr rfl (fun A _ => ?_)
      have hinner : opArc ψ hψ (sigmaStrataFinset A) f hf x
          = ∑ β ∈ sigmaStrataFinset A, g β x := by
        rw [opArc_eq_sum_singletons, Finset.sum_apply]
      rw [hinner]
    rw [hcongr]
    exact norm_sum_strata_sq_le (P := P) (γ := sigmaStrataFinset) (c := εs) hεs
      (fun E hE => Finset.subset_biUnion_of_mem _ hE) x
  have hLHSsum' : Summable fun x : ℤ =>
      (‖∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x‖ ^ 2) ^ r :=
    summable_pow_of_le_mul (r := r)
      (T := fun x : ℤ => ‖∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x‖ ^ 2)
      (W := W₁) (N := (P.card : ℝ) ^ 2 * (b₁.card : ℝ)) (by positivity) hW₁sum
      (fun x => Finset.sum_nonneg (f := fun β => ‖g β x‖ ^ 2) (fun β _ => sq_nonneg _))
      (fun x => sq_nonneg _) hLHSle (by omega)
  have hLHSsum : Summable fun x : ℤ =>
      ‖∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x‖ ^ (2 * r) :=
    Summable.congr hLHSsum' (fun x => by rw [← pow_mul])
  -- ### summability on the right
  have hRHSbound : ∀ A₀ ∈ P, ∀ x : ℤ,
      (∑ α ∈ strataCompFinset S k A₀,
          ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2)
        ≤ (((sigmaStrataFinset A₀).card : ℝ) ^ 2 * ((strataCompFinset S k A₀).card : ℝ)) *
          (∑ β ∈ (strataCompFinset S k A₀).biUnion
              (fun α => (sigmaStrataFinset A₀).image (fun γ => γ + α)), ‖g β x‖ ^ 2) := by
    intro A₀ _ x
    have h := sum_opArc_shift_sq_le (E := sigmaStrataFinset A₀) (C := strataCompFinset S k A₀)
      hψ hf x
    simpa [hgdef] using h
  have hRHSsum : ∀ A₀ ∈ P, Summable fun x : ℤ =>
      (∑ α ∈ strataCompFinset S k A₀,
        ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2) ^ r := by
    intro A₀ hA₀
    set b₂ : Finset Work.BourgainPlan.IonescuWainger.Circle := (strataCompFinset S k A₀).biUnion
      (fun α => (sigmaStrataFinset A₀).image (fun γ => γ + α)) with hb₂def
    set W₂ : ℤ → ℝ := fun x => ∑ β ∈ b₂, ‖g β x‖ ^ 2 with hW₂def
    have hW₂sum : Summable W₂ := by
      rw [hW₂def]
      exact summable_finset_sq_norm hg
    have hb : ∀ x : ℤ, (∑ α ∈ strataCompFinset S k A₀,
          ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2)
        ≤ (((sigmaStrataFinset A₀).card : ℝ) ^ 2 *
            ((strataCompFinset S k A₀).card : ℝ)) * W₂ x := by
      intro x
      rw [hW₂def]
      simpa [hb₂def] using hRHSbound A₀ hA₀ x
    exact summable_pow_of_le_mul (r := r)
      (T := fun x : ℤ => ∑ α ∈ strataCompFinset S k A₀,
        ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2)
      (W := W₂) (N := ((sigmaStrataFinset A₀).card : ℝ) ^ 2 *
        ((strataCompFinset S k A₀).card : ℝ)) (by positivity) hW₂sum
      (fun x => Finset.sum_nonneg (f := fun β => ‖g β x‖ ^ 2) (fun β _ => sq_nonneg _))
      (fun x => Finset.sum_nonneg
        (f := fun α => ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2)
        (fun α _ => sq_nonneg _)) hb (by omega)
  -- ### passing to `ℝ≥0∞`
  set LHSr : ℝ := ∑' x : ℤ, ‖∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x‖ ^ (2 * r)
    with hLHSrdef
  set RHSr : ℝ := ∑ A₀ ∈ P, ∑' x : ℤ,
      (∑ α ∈ strataCompFinset S k A₀,
        ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2) ^ r with hRHSrdef
  have hreal' : LHSr ≤ C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r * RHSr := by
    rw [hLHSrdef, hRHSrdef]
    simpa only [hPdef] using hreal
  have hLHSconv : (∑' x : ℤ, ENNReal.ofReal
        (‖∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x‖ ^ (2 * r)))
      = ENNReal.ofReal LHSr := by
    rw [hLHSrdef]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun x => pow_nonneg (norm_nonneg _) (2 * r)) hLHSsum).symm
  have hRHSconv : ENNReal.ofReal RHSr
      = ∑ A₀ ∈ P, ∑' x : ℤ,
          (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2))
            ^ (r : ℝ) := by
    rw [hRHSrdef]
    rw [ENNReal.ofReal_sum_of_nonneg (fun A₀ hA₀ => tsum_nonneg (fun x => pow_nonneg
      (Finset.sum_nonneg
        (f := fun α => ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2)
        (fun α _ => sq_nonneg _)) r))]
    refine Finset.sum_congr rfl (fun A₀ hA₀ => ?_)
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => pow_nonneg
        (Finset.sum_nonneg
          (f := fun α => ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2)
          (fun α _ => sq_nonneg _)) r) (hRHSsum A₀ hA₀)]
    refine tsum_congr (fun x => ?_)
    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_sum_of_nonneg (fun α _ => sq_nonneg _),
      ← ENNReal.ofReal_pow (Finset.sum_nonneg
        (f := fun α => ‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2)
        (fun α _ => sq_nonneg _)) r]
  have hc0 : 0 ≤ C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r := by positivity
  calc ∑' x : ℤ, ENNReal.ofReal
        (‖∑ A ∈ P, εs A * opArc ψ hψ (sigmaStrataFinset A) f hf x‖ ^ (2 * r))
      = ENNReal.ofReal LHSr := hLHSconv
    _ ≤ ENNReal.ofReal (C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r * RHSr) :=
        ENNReal.ofReal_le_ofReal hreal'
    _ = ENNReal.ofReal (C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r) *
          ∑ A₀ ∈ P, ∑' x : ℤ,
            (∑ α ∈ strataCompFinset S k A₀,
              ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) f hf x‖ ^ 2))
              ^ (r : ℝ) := by
        rw [ENNReal.ofReal_mul hc0, hRHSconv]

end Work.IonescuWainger
