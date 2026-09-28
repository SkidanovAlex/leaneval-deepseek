import Mathlib
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.LatRecurse.ncard_int_interval

/-!
# Auxiliary material for the recursive lattice-point count `Work.HP.FM.latStep_count`

Given a `RecData D` (an injective real presentation `D.Φ` of a rank-`R` lattice, a shortest
primitive coefficient vector `D.u` and a complementary family `D.v` completing `u` to a
`ℤ`-basis of `ℤ^R`), the *decomposition map*

  `D.decompFun : ℤ × (Fin (R-1) → ℤ) → (Fin R → ℤ),  (a, t) ↦ a • u + ∑ i, t i • v i`

is a bijection (this is the `bij` field of the structure).  We record its inverse as
`D.coords : ℤ^R → ℤ × ℤ^(R-1)` and prove the basic facts needed for the fibre count
`Work.HP.FM.latStep_count`, namely

* `D.step (fun j => (D.coords x).2 j)` is the orthogonal projection of `D.Φ x` onto `D.p^⊥`
  (`D.step_coords`), so the `t`-coordinate of a lattice point of `D.Φ`-norm `≤ T` is a
  lattice point of `D.step` of norm `≤ T` (`coords_snd_mem_latSet_step`);
* `D.step` is injective (`step_injective`), so that `latSet D.step T` is finite
  (`latSet` of an injective presentation); and
* `D.p ≠ 0` (`p_ne_zero`).
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.FM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}

/-- The `ℤ`-linear decomposition-of-a-vector map attached to a `RecData`: it sends the pair of
coordinates `(a, t)` to `a • u + ∑ i, t i • v i ∈ ℤ^R`. -/
def RecData.decompFun (D : RecData R ι) : ℤ × (Fin (R - 1) → ℤ) → (Fin R → ℤ) :=
  fun c => c.1 • D.u + ∑ i, c.2 i • D.v i

/-- The decomposition map of a `RecData` is bijective (it is the `bij` field). -/
lemma RecData.bijective_decompFun (D : RecData R ι) : Function.Bijective D.decompFun := by
  unfold RecData.decompFun
  exact D.bij

/-- The decomposition map as an equivalence. -/
def RecData.decompEquiv (D : RecData R ι) : (ℤ × (Fin (R - 1) → ℤ)) ≃ (Fin R → ℤ) :=
  Equiv.ofBijective D.decompFun D.bijective_decompFun

/-- The coordinates of `x : ℤ^R` in the `ℤ`-basis `(u, v)`: the inverse of the decomposition
map. -/
def RecData.coords (D : RecData R ι) : (Fin R → ℤ) → ℤ × (Fin (R - 1) → ℤ) :=
  D.decompEquiv.symm

lemma RecData.decompFun_injective (D : RecData R ι) : Function.Injective D.decompFun :=
  D.bij.1

lemma RecData.decompFun_coords (D : RecData R ι) (x : Fin R → ℤ) :
    D.decompFun (D.coords x) = x := by
  have h := Equiv.apply_symm_apply (D.decompEquiv) x
  have h2 : (D.decompEquiv : (ℤ × (Fin (R - 1) → ℤ)) → (Fin R → ℤ)) (D.decompEquiv.symm x)
      = D.decompFun (D.decompEquiv.symm x) := rfl
  rw [h2] at h
  rw [RecData.coords]
  exact h

lemma RecData.coords_injective (D : RecData R ι) : Function.Injective D.coords :=
  D.decompEquiv.symm.injective

lemma RecData.coords_decompFun (D : RecData R ι) (a : ℤ) (t : Fin (R - 1) → ℤ) :
    D.coords (D.decompFun (a, t)) = (a, t) :=
  D.decompFun_injective (D.decompFun_coords (D.decompFun (a, t)))

/-- Membership in the image of `D.coords`, spelled out through the decomposition map. -/
lemma RecData.mem_coords_image (D : RecData R ι) (S : Set (Fin R → ℤ)) (a : ℤ)
    (t : Fin (R - 1) → ℤ) :
    (a, t) ∈ D.coords '' S ↔ D.decompFun (a, t) ∈ S := by
  constructor
  · rintro ⟨x, hx, hxx⟩
    rw [← hxx, D.decompFun_coords]
    exact hx
  · intro h
    exact ⟨D.decompFun (a, t), h, D.coords_decompFun a t⟩

/-- The shortest vector `D.p` of the presented lattice is nonzero. -/
lemma RecData.p_ne_zero (D : RecData R ι) : D.p ≠ 0 := by
  intro hp
  refine D.u_ne ?_
  have h : (fun k => (D.u k : ℝ)) = 0 := by
    apply D.Φ_inj
    rw [RecData.p] at hp
    simpa using hp
  ext j
  have := congrFun h j
  simpa using this

lemma RecData.norm_p_pos (D : RecData R ι) : 0 < ‖D.p‖ :=
  norm_pos_iff.mpr D.p_ne_zero

/-- The projected step map, evaluated at a real coefficient vector: it is the orthogonal
projection of `Φ (∑ j, x j • v j)` onto `p^⊥`. -/
lemma RecData.step_apply_real (D : RecData R ι) (x : Fin (R - 1) → ℝ) :
    D.step x = projU D.p (D.Φ (∑ j, x j • (fun k => (D.v j k : ℝ)))) := by
  rw [RecData.step, latStep_apply, map_sum, map_sum]
  simp only [map_smul, RecData.p]

/-- The kernel of the projected step map is trivial. -/
lemma RecData.step_eq_zero (D : RecData R ι) (x : Fin (R - 1) → ℝ) (hx : D.step x = 0) :
    x = 0 := by
  have h1 : projU D.p (D.Φ (∑ j, x j • (fun k => (D.v j k : ℝ)))) = 0 := by
    rw [← D.step_apply_real]; exact hx
  have hmem : D.Φ (∑ j, x j • (fun k => (D.v j k : ℝ))) ∈ Submodule.span ℝ {D.p} :=
    (projU_eq_zero_iff D.p D.p_ne_zero _).mp h1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hzero : (∑ j, x j • (fun k => (D.v j k : ℝ))) - c • (fun k => (D.u k : ℝ)) = 0 := by
    apply D.Φ_inj
    rw [map_sub, map_smul, ← hc, RecData.p, sub_self, map_zero]
  have h2 : ((-c) • (fun j => (D.u j : ℝ)) + ∑ i, x i • (fun j => (D.v i j : ℝ))) = 0 := by
    rw [neg_smul, show (-(c • (fun j => (D.u j : ℝ))) + ∑ i, x i • (fun j => (D.v i j : ℝ)))
        = (∑ i, x i • (fun j => (D.v i j : ℝ))) - c • (fun j => (D.u j : ℝ)) from by
          rw [sub_eq_add_neg, add_comm]]
    exact hzero
  have hind := D.indep (-c, x) h2
  exact congrArg Prod.snd hind

/-- The projected step map is injective. -/
lemma RecData.step_injective (D : RecData R ι) : Function.Injective D.step := by
  intro t t' h
  have hker : D.step (t - t') = 0 := by rw [map_sub, h, sub_self]
  have hz : t - t' = 0 := D.step_eq_zero (t - t') hker
  exact sub_eq_zero.mp hz

/-- Peeling off `p`: the projected map applied to the `v`-coordinates of `x` is the orthogonal
projection of `Φ x` onto `p^⊥`. -/
lemma RecData.step_coords (D : RecData R ι) (x : Fin R → ℤ) :
    D.step (fun j => ((D.coords x).2 j : ℝ)) = projU D.p (D.Φ (fun k => (x k : ℝ))) := by
  have hdecomp : D.decompFun (D.coords x) = x := D.decompFun_coords x
  have hx : (fun k => (x k : ℝ))
      = (fun k => ((∑ j, (D.coords x).2 j • D.v j) k : ℝ))
        + ((D.coords x).1 : ℝ) • (fun k => (D.u k : ℝ)) := by
    ext k
    have hk := congrFun hdecomp k
    rw [← hk]
    simp only [RecData.decompFun, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    push_cast
    ring
  have hstep : projU D.p (D.Φ (fun k => ((∑ j, (D.coords x).2 j • D.v j) k : ℝ)))
      = projU D.p (D.Φ (fun k => (x k : ℝ))) := by
    rw [hx, map_add, map_smul,
      show (D.Φ (fun k => (D.u k : ℝ))) = D.p from rfl, projU_add_smul]
  rw [D.step_cast]
  exact hstep

/-- The `t`-coordinates of the lattice points of `D.Φ` of norm `≤ T` are lattice points of
`D.step` of norm `≤ T`. -/
lemma RecData.coords_snd_mem_latSet_step (D : RecData R ι) {T : ℝ} {x : Fin R → ℤ}
    (hx : x ∈ latSet D.Φ T) : (D.coords x).2 ∈ latSet D.step T := by
  rw [latSet, Set.mem_ofPred_eq] at hx ⊢
  rw [D.step_coords x]
  exact le_trans (norm_projU_le _ _) hx

/-- The integers `a` with `|(a : ℝ) + c| ≤ M` form a finite set. -/
lemma finite_int_abs_add_le (c M : ℝ) : {a : ℤ | |(a : ℝ) + c| ≤ M}.Finite := by
  refine (Set.finite_Icc ⌈-M - c⌉ ⌊M - c⌋).subset ?_
  intro a ha
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le] at ha ⊢
  exact ⟨Int.ceil_le.mpr (by linarith [ha.1]), Int.le_floor.mpr (by linarith [ha.2])⟩

/-- Counting integers `a` all of which satisfy `|(a : ℝ) + c| ≤ M`. -/
lemma ncard_le_int_interval {S : Set ℤ} {c M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a ∈ S, |(a : ℝ) + c| ≤ M) :
    S.ncard ≤ Nat.floor (2 * M) + 1 :=
  le_trans (Set.ncard_le_ncard (fun a ha => h a ha) (finite_int_abs_add_le c M))
    (Work.HP.LatRecurse.ncard_int_interval hM)

/-- The set of coefficient vectors of lattice points of norm `≤ T` is finite, for an injective
presentation.  (Injectivity gives an antilipschitz constant, so the norm of `Φ` bounds all
coordinates, and the set sits inside a finite box.) -/
lemma latSet_finite_of_injective {m : ℕ} (Ψ : LatMap (ι := ι) m) (hΨ : Function.Injective Ψ)
    (T : ℝ) : (latSet Ψ T).Finite := by
  classical
  obtain ⟨K, -, hK⟩ := Ψ.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hΨ)
  refine (Set.Finite.pi fun _ : Fin m => Set.finite_Icc (-⌈(K : ℝ) * T⌉) ⌈(K : ℝ) * T⌉).subset ?_
  intro t ht
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hb : |(t i : ℝ)| ≤ (K : ℝ) * T := by
    have h1 : ‖(t i : ℝ)‖ ≤ ‖fun j : Fin m => (t j : ℝ)‖ :=
      norm_le_pi_norm (fun j : Fin m => (t j : ℝ)) i
    have h2 : ‖fun j : Fin m => (t j : ℝ)‖ ≤ (K : ℝ) * ‖Ψ (fun j : Fin m => (t j : ℝ))‖ := by
      have := hK.le_mul_dist (fun j : Fin m => (t j : ℝ)) 0
      simpa [dist_zero_right, map_zero] using this
    calc |(t i : ℝ)| = ‖(t i : ℝ)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fun j : Fin m => (t j : ℝ)‖ := h1
      _ ≤ (K : ℝ) * ‖Ψ (fun j : Fin m => (t j : ℝ))‖ := h2
      _ ≤ (K : ℝ) * T := mul_le_mul_of_nonneg_left ht K.coe_nonneg
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  constructor
  · have hcast : ((-⌈(K : ℝ) * T⌉ : ℤ) : ℝ) ≤ ((t i : ℤ) : ℝ) := by
      push_cast
      calc -(⌈(K : ℝ) * T⌉ : ℝ) ≤ -((K : ℝ) * T) := neg_le_neg (Int.le_ceil _)
        _ ≤ (t i : ℝ) := hlo
    exact Int.cast_le.mp hcast
  · have hcast : ((t i : ℤ) : ℝ) ≤ ((⌈(K : ℝ) * T⌉ : ℤ) : ℝ) := hhi.trans (Int.le_ceil _)
    exact Int.cast_le.mp hcast

/-- The lattice points of the projected step presentation of norm `≤ T` form a finite set. -/
lemma RecData.step_latSet_finite (D : RecData R ι) (T : ℝ) : (latSet D.step T).Finite :=
  latSet_finite_of_injective D.step D.step_injective T

/-- **The fibre bound.**  For a fixed `t`, the integers `a` for which `a • u + ∑ i, t i • v i`
is a lattice point of `D.Φ` of norm `≤ T` number at most `⌊2T/‖D.p‖⌋ + 1`: writing
`Φ (a • u + ∑ t i • v i) = a • p + z` with `z = Φ (∑ t i • v i)`, Pythagoras gives
`(⟪z,p⟫/‖p‖² + a)² ‖p‖² ≤ ‖Φ (…)‖² ≤ T²`, so all these `a` lie in an interval of length
`2T/‖p‖`. -/
theorem fiber_ncard_le (D : RecData R ι) {T : ℝ} (hT : 0 ≤ T) (t : Fin (R - 1) → ℤ) :
    {a : ℤ | D.decompFun (a, t) ∈ latSet D.Φ T}.ncard
      ≤ Nat.floor (2 * (T / ‖D.p‖)) + 1 := by
  classical
  set z : EuclideanSpace ℝ ι := D.Φ (fun k => ((∑ i, t i • D.v i) k : ℝ)) with hz
  have hM : 0 ≤ T / ‖D.p‖ := div_nonneg hT (norm_nonneg _)
  refine ncard_le_int_interval (c := inner ℝ z D.p / ‖D.p‖ ^ 2) (M := T / ‖D.p‖) hM ?_
  intro a ha
  have hnorm : ‖z + (a : ℝ) • D.p‖ ≤ T := by
    have h : ‖D.Φ (fun k => ((a • D.u + ∑ i, t i • D.v i) k : ℝ))‖ ≤ T := ha
    rw [D.Phi_cast_bij] at h
    simpa [hz, add_comm] using h
  have h2 : ‖z + (a : ℝ) • D.p‖ ^ 2 ≤ T ^ 2 := by
    nlinarith [hnorm, hT, norm_nonneg (z + (a : ℝ) • D.p)]
  have hc2 : (inner ℝ z D.p / ‖D.p‖ ^ 2 + (a : ℝ)) ^ 2 * ‖D.p‖ ^ 2 ≤ T ^ 2 := by
    have hpyth := norm_sq_add_smul D.p (a : ℝ) z
    nlinarith [hpyth, h2, sq_nonneg ‖projU D.p z‖]
  have h4 : ((inner ℝ z D.p / ‖D.p‖ ^ 2 + (a : ℝ)) * ‖D.p‖) ^ 2 ≤ T ^ 2 := by
    rw [mul_pow]; exact hc2
  have h5 : |(inner ℝ z D.p / ‖D.p‖ ^ 2 + (a : ℝ)) * ‖D.p‖| ≤ T := by
    have h := sq_le_sq.mp h4
    rwa [abs_of_nonneg hT] at h
  have h6 : |(inner ℝ z D.p / ‖D.p‖ ^ 2 + (a : ℝ))| * ‖D.p‖ ≤ T := by
    rwa [abs_mul, abs_of_nonneg (norm_nonneg _)] at h5
  rw [le_div_iff₀ D.norm_p_pos, add_comm]
  exact h6

end Work.HP.FM
