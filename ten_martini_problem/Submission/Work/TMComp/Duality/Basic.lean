import Mathlib
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# Aubry duality (C3): auxiliary lemmas

General analytic lemmas (spectral perturbation, resolvent bounds, density of finitely
supported vectors) and algebraic lemmas about `fibVec`, plus the bridge between
`amoSpec` and the concrete operator `amoOp`.
-/

open LeanEval.Analysis.TenMartini

open scoped ENNReal

noncomputable section

namespace Work.TMComp.Duality
instance instNontrivialEllTwo2 : Nontrivial EllTwo2 := by
  have hmem : Memℓp (fun p : ℤ × ℤ => if p = ((0, 0) : ℤ × ℤ) then (1 : ℂ) else 0)
      (2 : ℝ≥0∞) := by
    refine memℓp_gen ?_
    apply summable_of_ne_finset_zero (s := ({(0, 0)} : Finset (ℤ × ℤ)))
    intro p hp
    rw [if_neg (by simpa using hp), norm_zero]
    exact Real.zero_rpow (by norm_num)
  refine ⟨⟨fun p : ℤ × ℤ => if p = ((0, 0) : ℤ × ℤ) then (1 : ℂ) else 0, hmem⟩, 0, fun h => ?_⟩
  have h1 := congrArg (fun (v : EllTwo2) => (v : ℤ × ℤ → ℂ) (0, 0)) h
  simp at h1


/-! ## 1. Generic spectral analysis -/

section Spectral

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- If `E` is not in the spectrum of `A`, then `A - E` is bounded below. -/
theorem exists_lower_bound_of_notMem (A : X →L[ℂ] X) (E : ℝ)
    (hE : (E : ℂ) ∉ spectrum ℂ A) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : X, d * ‖x‖ ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) E) x‖ := by
  have hunit : IsUnit (algebraMap ℂ (X →L[ℂ] X) E - A) := spectrum.notMem_iff.mp hE
  obtain ⟨u, hu⟩ := hunit
  set C : ℝ := ‖(↑u⁻¹ : X →L[ℂ] X)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  refine ⟨1 / (C + 1), by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ C * ‖(algebraMap ℂ (X →L[ℂ] X) E - A) x‖ := by
    calc ‖x‖ = ‖((↑u⁻¹ : X →L[ℂ] X) * (algebraMap ℂ (X →L[ℂ] X) E - A)) x‖ := by
            rw [← hu, Units.inv_mul]; simp
      _ = ‖(↑u⁻¹ : X →L[ℂ] X) ((algebraMap ℂ (X →L[ℂ] X) E - A) x)‖ := by
            rw [mul_apply_eq_comp]
      _ ≤ C * ‖(algebraMap ℂ (X →L[ℂ] X) E - A) x‖ := ContinuousLinearMap.le_opNorm _ _
  have h2 : (algebraMap ℂ (X →L[ℂ] X) E - A) x = -((A - algebraMap ℂ (X →L[ℂ] X) E) x) := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
    abel
  rw [h2, norm_neg] at h1
  have hP : 0 ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) E) x‖ := norm_nonneg _
  have h3 : ‖x‖ ≤ (C + 1) * ‖(A - algebraMap ℂ (X →L[ℂ] X) E) x‖ := by nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < C + 1)]
  linarith [h3]

/-- A self-adjoint operator that is bounded below by a positive constant is invertible. -/
theorem isUnit_of_lower_bound [Nontrivial X] (A : X →L[ℂ] X) (hA : IsSelfAdjoint A) {d : ℝ}
    (hd : 0 < d) (h : ∀ x : X, d * ‖x‖ ≤ ‖A x‖) : IsUnit A := by
  have hker : A.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : A x = 0 := by simpa using hx
    have h1 := h x
    rw [hx0, norm_zero] at h1
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x, hd]
    exact norm_eq_zero.mp this
  have hdense : A.range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff]
    rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hA.isStarNormal, hker]
  have hanti : ∃ K, AntilipschitzWith K A :=
    ⟨⟨d⁻¹, le_of_lt (inv_pos.mpr hd)⟩, by
      apply ContinuousLinearMap.antilipschitz_of_bound
      intro x
      change ‖x‖ ≤ d⁻¹ * ‖A x‖
      rw [inv_mul_eq_div, le_div_iff₀ hd]
      linarith [h x]⟩
  have hbij : Function.Bijective A :=
    (ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz A).mpr ⟨hdense, hanti⟩
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr hbij

/-- Spectral perturbation: a spectral point of `A` is within `‖A - B‖` of the spectrum of a
self-adjoint `B`. -/
theorem spectrum_dist_le_of_norm_sub_le [Nontrivial X] (A B : X →L[ℂ] X)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {δ : ℝ} (h : ‖A - B‖ ≤ δ) {z : ℝ}
    (hz : (z : ℂ) ∈ spectrum ℂ A) : ∃ w ∈ spectrum ℂ B, ‖w - (z : ℂ)‖ ≤ δ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := (spectrum.isCompact B).exists_isMinOn (spectrum.nonempty B)
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) h
  have hd : 0 < ‖w₀ - (z : ℂ)‖ := lt_of_le_of_lt hδ0 (hcon w₀ hw₀mem)
  have hspec : ∀ w ∈ spectrum ℂ B, ‖w₀ - (z : ℂ)‖ ≤ ‖w - (z : ℂ)‖ := fun w hw => hw₀min hw
  have hlowerB : ∀ x : X, ‖w₀ - (z : ℂ)‖ * ‖x‖
      ≤ ‖(B - algebraMap ℂ (X →L[ℂ] X) z) x‖ :=
    TMC7Core.Scale.norm_le_of_spectrum_avoid B hB z hd hspec
  have hlowerA : ∀ x : X, (‖w₀ - (z : ℂ)‖ - δ) * ‖x‖
      ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ := by
    intro x
    have hdecomp : (B - algebraMap ℂ (X →L[ℂ] X) z) x
        = (A - algebraMap ℂ (X →L[ℂ] X) z) x - (A - B) x := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.sub_apply]
      abel
    have h3 : ‖(A - B) x‖ ≤ ‖A - B‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    have h4 : ‖(B - algebraMap ℂ (X →L[ℂ] X) z) x‖
        ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ + ‖A - B‖ * ‖x‖ := by
      rw [hdecomp]; exact le_trans (norm_sub_le _ _) (by linarith)
    nlinarith [hlowerB x, h4, h, norm_nonneg x]
  have hpos : 0 < ‖w₀ - (z : ℂ)‖ - δ := sub_pos.mpr (hcon w₀ hw₀mem)
  have hzsa : IsSelfAdjoint ((z : ℂ)) := by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  have hunit : IsUnit (A - algebraMap ℂ (X →L[ℂ] X) z) :=
    isUnit_of_lower_bound _ (hA.sub (IsSelfAdjoint.algebraMap _ hzsa)) hpos hlowerA
  have hnotunit : ¬ IsUnit (algebraMap ℂ (X →L[ℂ] X) z - A) := spectrum.mem_iff.mp hz
  refine hnotunit ?_
  have : algebraMap ℂ (X →L[ℂ] X) z - A = -(A - algebraMap ℂ (X →L[ℂ] X) z) := by abel
  rw [this]
  exact hunit.neg

/-- A vector with small relative residual for a self-adjoint operator produces a nearby
spectral point. -/
theorem spectrum_close [Nontrivial X] (A : X →L[ℂ] X) (hA : IsSelfAdjoint A) (z : ℝ)
    (x : X) (hx : x ≠ 0) :
    ∃ w ∈ spectrum ℂ A, ‖w - (z : ℂ)‖ ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ / ‖x‖ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := (spectrum.isCompact A).exists_isMinOn (spectrum.nonempty A)
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  have hd : 0 < ‖w₀ - (z : ℂ)‖ := lt_of_le_of_lt (by positivity) (hcon w₀ hw₀mem)
  have hspec : ∀ w ∈ spectrum ℂ A, ‖w₀ - (z : ℂ)‖ ≤ ‖w - (z : ℂ)‖ := fun w hw => hw₀min hw
  have hlb := TMC7Core.Scale.norm_le_of_spectrum_avoid A hA z hd hspec x
  have hle : ‖w₀ - (z : ℂ)‖ * ‖x‖ ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ := hlb
  have key : ‖w₀ - (z : ℂ)‖ ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ / ‖x‖ := by
    rw [le_div_iff₀ (norm_pos_iff.mpr hx)]
    linarith [hle]
  exact absurd key (not_le.mpr (hcon w₀ hw₀mem))

end Spectral

/-! ## 2. `fibVec` algebra -/

theorem fibVec_eq_of_support (ϑ : ℝ) (f : ℤ × ℤ → ℂ) {s t : Finset (ℤ × ℤ)}
    (hs : ∀ p : ℤ × ℤ, p ∉ s → f p = 0) (ht : ∀ p : ℤ × ℤ, p ∉ t → f p = 0) :
    fibVec ϑ f s = fibVec ϑ f t := by
  have key : ∀ u : Finset (ℤ × ℤ), u ⊆ s ∪ t → (∀ p : ℤ × ℤ, p ∉ u → f p = 0) →
      fibVec ϑ f u = fibVec ϑ f (s ∪ t) := by
    intro u hsub hu
    refine lp.ext (funext fun n => ?_)
    rw [fibVec_coord, fibVec_coord]
    refine Finset.sum_subset (Finset.filter_subset_filter _ hsub) ?_
    intro p hp hpu
    have hp' : p ∉ u := fun h => hpu (Finset.mem_filter.mpr ⟨h, (Finset.mem_filter.mp hp).2⟩)
    rw [hu p hp', mul_zero]
  rw [key s (Finset.subset_union_left) hs, key t (Finset.subset_union_right) ht]

theorem fibVec_sub (ϑ : ℝ) (f g : ℤ × ℤ → ℂ) (s : Finset (ℤ × ℤ)) :
    fibVec ϑ (f - g) s = fibVec ϑ f s - fibVec ϑ g s := by
  refine lp.ext (funext fun n => ?_)
  show (∑ p ∈ s.filter (fun p => p.2 = n), phR ((p.1 : ℝ) * ϑ) * (f - g) p)
      = (fibVec ϑ f s - fibVec ϑ g s) n
  rw [lp.coeFn_sub, Pi.sub_apply, fibVec_coord, fibVec_coord]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem fibVec_add (ϑ : ℝ) (f g : ℤ × ℤ → ℂ) (s : Finset (ℤ × ℤ)) :
    fibVec ϑ (f + g) s = fibVec ϑ f s + fibVec ϑ g s := by
  refine lp.ext (funext fun n => ?_)
  show (∑ p ∈ s.filter (fun p => p.2 = n), phR ((p.1 : ℝ) * ϑ) * (f + g) p)
      = (fibVec ϑ f s + fibVec ϑ g s) n
  rw [lp.coeFn_add, Pi.add_apply, fibVec_coord, fibVec_coord]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem fibVec_const_mul (ϑ : ℝ) (c : ℂ) (f : ℤ × ℤ → ℂ) (s : Finset (ℤ × ℤ)) :
    fibVec ϑ (fun p => c * f p) s = c • fibVec ϑ f s := by
  refine lp.ext (funext fun n => ?_)
  show (∑ p ∈ s.filter (fun p => p.2 = n), phR ((p.1 : ℝ) * ϑ) * (c * f p))
      = (c • fibVec ϑ f s) n
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, fibVec_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The norm of a finitely supported vector is the sum of the squares of its coordinates. -/
theorem norm_sq_eq_sum (v : EllTwo2) (s : Finset (ℤ × ℤ)) (hs : ∀ p : ℤ × ℤ, p ∉ s → v p = 0) :
    ‖v‖ ^ 2 = ∑ p ∈ s, ‖v p‖ ^ 2 := by
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  have hts : (∑' i : ℤ × ℤ, ‖(v : ℤ × ℤ → ℂ) i‖ ^ 2)
      = ∑ p ∈ s, ‖(v : ℤ × ℤ → ℂ) p‖ ^ 2 := by
    rw [tsum_eq_sum]
    intro p hp
    rw [hs p hp, norm_zero]
    norm_num
  calc ‖v‖ ^ 2 = ‖v‖ ^ ((2 : ℝ≥0∞).toReal) := by norm_num
    _ = ∑' i : ℤ × ℤ, ‖(v : ℤ × ℤ → ℂ) i‖ ^ ((2 : ℝ≥0∞).toReal) :=
        lp.norm_rpow_eq_tsum (by norm_num) v
    _ = ∑' i : ℤ × ℤ, ‖(v : ℤ × ℤ → ℂ) i‖ ^ 2 := tsum_congr fun i => by norm_num
    _ = ∑ p ∈ s, ‖(v : ℤ × ℤ → ℂ) p‖ ^ 2 := hts

/-- A finite set of pairs is contained in a "box" whose `m`-range has diameter `< N`, and
whose one-step expansion is contained in `2N` consecutive integers. -/
theorem exists_box (s : Finset (ℤ × ℤ)) :
    ∃ a : ℤ, ∃ N : ℕ, 0 < N ∧ 2 ≤ N ∧ (∀ p ∈ s, p.1 ∈ Set.Icc a (a + (N : ℤ) - 1)) ∧
      (∀ p ∈ s, p.1 ∈ Set.Icc (a - 1) (a - 1 + 2 * (N : ℤ) - 1)) := by
  set S : ℕ := ∑ p ∈ s, p.1.natAbs with hS
  have hle : ∀ p ∈ s, p.1.natAbs ≤ S := by
    intro p hp
    rw [hS]
    exact Finset.single_le_sum (f := fun q : ℤ × ℤ => q.1.natAbs) (fun q _ => Nat.zero_le _) hp
  refine ⟨-(S : ℤ), 2 * S + 3, by omega, by omega, ?_, ?_⟩
  · intro p hp
    have h1 : (p.1.natAbs : ℤ) ≤ (S : ℤ) := Int.ofNat_le.mpr (hle p hp)
    constructor <;> omega
  · intro p hp
    have h1 : (p.1.natAbs : ℤ) ≤ (S : ℤ) := Int.ofNat_le.mpr (hle p hp)
    constructor <;> omega

/-- A finite set of pairs is contained in a square box of side `N`. -/
theorem exists_box2 (s : Finset (ℤ × ℤ)) :
    ∃ a b : ℤ, ∃ N : ℕ, 0 < N ∧ 2 ≤ N ∧
      (∀ p ∈ s, p.1 ∈ Set.Icc a (a + (N : ℤ) - 1) ∧
        p.2 ∈ Set.Icc b (b + (N : ℤ) - 1)) := by
  set S : ℕ := ∑ p ∈ s, (p.1.natAbs + p.2.natAbs) with hS
  have hle : ∀ p ∈ s, p.1.natAbs + p.2.natAbs ≤ S := by
    intro p hp
    rw [hS]
    exact Finset.single_le_sum (f := fun q : ℤ × ℤ => q.1.natAbs + q.2.natAbs)
      (fun q _ => Nat.zero_le _) hp
  have hmem : ∀ p ∈ s, p.1 ∈ Set.Icc (-(S : ℤ)) (-(S : ℤ) + ((2 * S + 3 : ℕ) : ℤ) - 1) ∧
      p.2 ∈ Set.Icc (-(S : ℤ)) (-(S : ℤ) + ((2 * S + 3 : ℕ) : ℤ) - 1) := by
    intro p hp
    have h1 : p.1.natAbs ≤ S := by have := hle p hp; omega
    have h2 : p.2.natAbs ≤ S := by have := hle p hp; omega
    have h3 : |p.1| ≤ (S : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    have h4 : |p.2| ≤ (S : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
    have h5 : -(p.1) ≤ |p.1| := neg_le_abs p.1
    have h6 : p.1 ≤ |p.1| := le_abs_self p.1
    have h7 : -(p.2) ≤ |p.2| := neg_le_abs p.2
    have h8 : p.2 ≤ |p.2| := le_abs_self p.2
    constructor <;> constructor <;> omega
  exact ⟨-(S : ℤ), -(S : ℤ), 2 * S + 3, by omega, by omega, hmem⟩

/-- The second coordinate of the support of `suspA` is contained in `[b-1, b+M]` when the
input's second coordinate lies in `[b, b + M - 1]`. -/
theorem suspA_support_n (α lam : ℝ) (f : EllTwo2) (b : ℤ) (M : ℕ) (hM : 0 < M)
    (hf : ∀ p : ℤ × ℤ, f p ≠ 0 → p.2 ∈ Set.Icc b (b + (M : ℤ) - 1)) :
    ∀ p : ℤ × ℤ, suspA α lam f p ≠ 0 → p.2 ∈ Set.Icc (b - 1) (b + (M : ℤ)) := by
  intro p hp
  obtain ⟨m, n⟩ := p
  rw [suspA_coord] at hp
  have h1 : f (m, n + 1) ≠ 0 ∨ f (m, n - 1) ≠ 0 ∨ f (m - 1, n) ≠ 0 ∨ f (m + 1, n) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp (by rw [h.1, h.2.1, h.2.2.1, h.2.2.2]; ring)
  rcases h1 with h | h | h | h
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; constructor <;> omega
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; constructor <;> omega
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; constructor <;> omega
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; constructor <;> omega

/-- The bridge between the abstract `amoSpec` (an `∃ H` statement) and the concrete
operator `amoOp α lam 0`. -/
theorem mem_amoSpec_iff (α lam E : ℝ) :
    E ∈ Work.TMContract.amoSpec α lam ↔ (E : ℂ) ∈ spectrum ℂ (amoOp α lam 0) := by
  constructor
  · rintro ⟨H, hH, hspec⟩
    rwa [amoOp_unique hH] at hspec
  · intro h
    exact ⟨amoOp α lam 0, amoOp_isAMO α lam 0, h⟩

end Work.TMComp.Duality
