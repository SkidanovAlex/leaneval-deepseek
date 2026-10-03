import Mathlib
import Submission.Work.Peluse.Ulower.rankInduction
import Submission.Work.Peluse.Peel.boxNormPow_one_tsum
import Submission.Work.Peluse.LevelRaise.boxNormPow_succ_ge

set_option maxHeartbeats 3200000

/-!
# The window-sum aggregate bound (`Work.Peluse.Ulower.windowAggregate`)

The target is the "window-sum / Cauchy--Schwarz" step of Peluse's Lemma 7.5 (Forum Math. Pi **8**
(2020) e16, Lemma 7.5), in the shape consumed by `Work.Peluse.Ulower.lemma75_control`:

```
C · (|Q^s|⁻¹)² ∑_{u,v ∈ Q^s} ‖L⁻¹ ∑_x cubeTerm u v f x‖² ≤ ‖f‖^{2^{s+1}}_{□^{s+1}_{Q,…,Q}([-L,L])}
```

with `Q = [1,D]`, `D ≤ L` and `f` supported in `[-L,L]`.  The proof combines

* the level-`(s+1)` box-norm identity `boxNormPow (s+1) Q S f = boxScaling · normSqSum` of
  `Submission.Work.Peluse.LevelRaise.boxNormPow_succ_ge`, which writes the level-`(s+1)` box-norm
  power as the normalised sum of the squared `ℓ²`-norms of the *window sums* of the level-`s` cube
  terms `G_{uv} = cubeTerm s u v f`;
* the base case of the rank induction `norm_tsum_sq_le_windowSum` of
  `Submission.Work.Peluse.Ulower.rankInduction`, which bounds `‖∑_x G_{uv} x‖²` by the `ℓ²`-norm of
  the window sums of `G_{uv}` over the shift set `[1,D]`;
* the elementary support bookkeeping (`cubeTerm u v f` is supported in `[-L-sD, L+sD]`) and the
  arithmetic `(2L+1)(2(L+sD+D)+1) ≤ (6s+16)L²`, valid for `D ≤ L`.
-/

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-! ## Elementary index and support facts -/

/-- `arithIcc 1 D` is the integer interval `[1,D]`. -/
lemma arithIcc_one_eq (D : ℕ) : Work.Peluse.arithIcc 1 D = Finset.Icc (1 : ℤ) (D : ℤ) := by
  ext z
  rw [Work.Peluse.Ulower.mem_arithIcc_one, Finset.mem_Icc]

/-- The cardinality of the direction set `[1,D]^s`. -/
lemma card_piFinset_arithIcc (s D : ℕ) :
    (Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)).card = D ^ s := by
  rw [Fintype.card_piFinset]
  simp [Work.Peluse.Ulower.card_arithIcc_one, Finset.prod_const]

/-- An element of `arithIcc 1 D` has absolute value at most `D`. -/
lemma natAbs_le_of_mem_arithIcc {D : ℕ} {a : ℤ} (ha : a ∈ Work.Peluse.arithIcc 1 D) :
    a.natAbs ≤ D := by
  rw [Work.Peluse.Ulower.mem_arithIcc_one] at ha
  have h1 : (0 : ℤ) ≤ a := by linarith [ha.1]
  have h2 : ((a.natAbs : ℤ)) ≤ ((D : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h1]
    exact ha.2
  exact_mod_cast h2

/-- The sum over the `piFinset` of a constant family is the sum over the corresponding family of
subtypes. -/
lemma sum_piFinset_eq_sum_subtype {s D : ℕ} (F : (Fin s → ℤ) → ℝ) :
    ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D), F u
      = ∑ g : (Fin s → {x : ℤ // x ∈ Work.Peluse.arithIcc 1 D}), F (fun i => (g i).1) := by
  classical
  have hπ : Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)
      = (Finset.univ : Finset (Fin s → {x : ℤ // x ∈ Work.Peluse.arithIcc 1 D})).image
          (fun g i => (g i).1) := by
    ext u
    simp only [Fintype.mem_piFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hu
      exact ⟨fun i => ⟨u i, hu i⟩, rfl⟩
    · rintro ⟨g, rfl⟩ i
      exact (g i).2
  rw [hπ, Finset.sum_image]
  intro x _ y _ h
  funext i
  exact Subtype.ext (congr_fun h i)

/-- The level-`(s+1)` box-norm power of the constant direction family `[1,D]`, expressed through
the sum of squares `normSqSum` of the *window sums* of the level-`s` cube terms. -/
lemma windowSum_eq_normSqSum (s D N : ℕ) (f : ℤ → ℂ) :
    (∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
        ∑ x ∈ Work.Peluse.BoxNorm.ball (s+1)
            (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) N,
          ‖∑ a ∈ Work.Peluse.arithIcc 1 D, Work.Peluse.cubeTerm u v f (x + a)‖ ^ 2)
      = Work.Peluse.BoxNorm.normSqSum (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) f N := by
  rw [Work.Peluse.BoxNorm.normSqSum]
  refine Eq.symm ?_
  have hconv : ∀ (hs hs' : (i : Fin s) → ↥(Work.Peluse.arithIcc 1 D)) (x : ℤ),
      (∑ a : ↥(Work.Peluse.arithIcc 1 D), Work.Peluse.BoxNorm.redCube
          (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) hs hs' f (x + ↑a))
        = (∑ a ∈ Work.Peluse.arithIcc 1 D, Work.Peluse.cubeTerm
            (fun i => (hs i).1) (fun i => (hs' i).1) f (x + a)) := by
    intro hs hs' x
    rw [Finset.sum_coe_sort (Work.Peluse.arithIcc 1 D)
      (fun a : ℤ => Work.Peluse.BoxNorm.redCube (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D)
          hs hs' f (x + a))]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  simp only [hconv]
  have h1 := sum_piFinset_eq_sum_subtype (s := s) (D := D)
    (fun u => ∑ hs' : (Fin s → ↥(Work.Peluse.arithIcc 1 D)),
      ∑ x ∈ Work.Peluse.BoxNorm.ball (s+1)
          (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) N,
        ‖∑ a ∈ Work.Peluse.arithIcc 1 D,
          Work.Peluse.cubeTerm u (fun i => (hs' i).1) f (x + a)‖ ^ 2)
  refine h1.symm.trans ?_
  refine Finset.sum_congr rfl (fun u _ => ?_)
  exact (sum_piFinset_eq_sum_subtype (s := s) (D := D)
    (fun v => ∑ x ∈ Work.Peluse.BoxNorm.ball (s+1)
        (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) N,
      ‖∑ a ∈ Work.Peluse.arithIcc 1 D, Work.Peluse.cubeTerm u v f (x + a)‖ ^ 2)).symm

/-- The level-`s` cube term of a function supported in `[-L,L]` with directions of absolute value
at most `D` is supported in `[-(L+sD), L+sD]`. -/
lemma supportIn_cubeTerm {s L D : ℕ} {f : ℤ → ℂ} (hsupp : Work.Peluse.SupportIn f L)
    {u v : Fin s → ℤ} (hv : ∀ i, (v i).natAbs ≤ D) :
    Work.Peluse.SupportIn (Work.Peluse.cubeTerm u v f) (L + s * D) := by
  intro x hx
  rw [Work.Peluse.cubeTerm]
  refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin s => false)) ?_
  have hcs : (Work.Peluse.cornerShift u v (fun _ : Fin s => false)).natAbs ≤ s * D := by
    rw [Work.Peluse.cornerShift]
    refine le_trans (Int.natAbs_sum_le _ _) ?_
    have step2 : (∑ i : Fin s, (if (fun _ : Fin s => false) i then u i else v i).natAbs)
        ≤ ∑ _i : Fin s, D :=
      Finset.sum_le_sum (fun i _ => by simpa using hv i)
    have step3 : (∑ _i : Fin s, D) = s * D := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact le_trans step2 (le_of_eq step3)
  have hx' : (x + Work.Peluse.cornerShift u v (fun _ : Fin s => false)).natAbs > L := by
    have h := Int.natAbs_add_le (x + Work.Peluse.cornerShift u v (fun _ : Fin s => false))
      (-(Work.Peluse.cornerShift u v (fun _ : Fin s => false)))
    have h2 : x + Work.Peluse.cornerShift u v (fun _ : Fin s => false)
        + -(Work.Peluse.cornerShift u v (fun _ : Fin s => false)) = x := by ring
    rw [h2, Int.natAbs_neg] at h
    omega
  rw [hsupp _ hx']
  simp

/-- The box-norm window for the constant direction family `[1,D]` dominates `L + sD + D`. -/
lemma le_rad_arithIcc (s L D : ℕ) (hD : 1 ≤ D) :
    L + s * D + D ≤ Work.Peluse.BoxNorm.rad (s+1)
      (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) (L + s * D) := by
  rw [Work.Peluse.BoxNorm.rad]
  have hmemD : (D : ℤ) ∈ Work.Peluse.arithIcc 1 D := by
    rw [Work.Peluse.Ulower.mem_arithIcc_one]
    exact ⟨by exact_mod_cast hD, le_rfl⟩
  have hDle : D ≤ (Work.Peluse.arithIcc 1 D).sum (fun z => z.natAbs) := by
    have h := Finset.single_le_sum
      (fun z (_ : z ∈ Work.Peluse.arithIcc 1 D) => Nat.zero_le z.natAbs) hmemD
    simpa using h
  have hsum : D ≤ ∑ _i : Fin (s+1), (Work.Peluse.arithIcc 1 D).sum (fun z => z.natAbs) := by
    have h1 : (∑ _i : Fin (s+1), (Work.Peluse.arithIcc 1 D).sum (fun z => z.natAbs))
        = (s+1) * (Work.Peluse.arithIcc 1 D).sum (fun z => z.natAbs) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [h1]
    calc D ≤ (Work.Peluse.arithIcc 1 D).sum (fun z => z.natAbs) := hDle
      _ = 1 * (Work.Peluse.arithIcc 1 D).sum (fun z => z.natAbs) := (one_mul _).symm
      _ ≤ (s+1) * (Work.Peluse.arithIcc 1 D).sum (fun z => z.natAbs) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le s))
  omega

/-- Off the box-norm window the window sum of a level-`s` cube term vanishes. -/
lemma sum_cubeTerm_window_eq_zero {s D L : ℕ} (hD : 1 ≤ D) {f : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn f L) {u v : Fin s → ℤ} (hv : ∀ i, (v i).natAbs ≤ D)
    {x : ℤ} (hx : x ∉ Work.Peluse.BoxNorm.ball (s+1)
        (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) (L + s * D)) :
    ∑ a ∈ Work.Peluse.arithIcc 1 D, Work.Peluse.cubeTerm u v f (x + a) = 0 := by
  refine Finset.sum_eq_zero (fun a ha => ?_)
  have haD : a.natAbs ≤ D := natAbs_le_of_mem_arithIcc ha
  have hb : Work.Peluse.SupportIn (Work.Peluse.cubeTerm u v f) (L + s * D) :=
    supportIn_cubeTerm (s := s) (L := L) (D := D) hsupp hv
  refine hb (x + a) ?_
  have hrad : L + s * D + D ≤ Work.Peluse.BoxNorm.rad (s+1)
      (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) (L + s * D) := le_rad_arithIcc s L D hD
  have hxrad : Work.Peluse.BoxNorm.rad (s+1)
      (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) (L + s * D) < x.natAbs := by
    by_contra h
    exact hx ((Work.Peluse.LevelRaise.mem_ball_iff
      (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) (L + s * D) x).mpr (not_lt.mp h))
  have htri : x.natAbs ≤ (x + a).natAbs + a.natAbs := by
    have h := Int.natAbs_add_le (x + a) (-a)
    have h2 : x + a + -a = x := by ring
    rw [h2, Int.natAbs_neg] at h
    exact h
  omega

/-- The window sums of the level-`s` cube terms over `[1,D]` vanish off the box-norm window, so
their squared `ℓ²`-norm is a finite sum over that window. -/
lemma tsum_windowSq_eq_sum_ball {s D L : ℕ} (hD : 1 ≤ D) {f : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn f L) {u v : Fin s → ℤ} (hv : ∀ i, (v i).natAbs ≤ D) :
    (∑' x : ℤ, ‖∑ a ∈ Work.Peluse.arithIcc 1 D, Work.Peluse.cubeTerm u v f (x + a)‖ ^ 2)
      = ∑ x ∈ Work.Peluse.BoxNorm.ball (s+1)
          (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) (L + s * D),
          ‖∑ a ∈ Work.Peluse.arithIcc 1 D, Work.Peluse.cubeTerm u v f (x + a)‖ ^ 2 := by
  refine tsum_eq_sum (fun x hx => ?_)
  rw [sum_cubeTerm_window_eq_zero hD hsupp hv hx]
  simp

/-- The normalising constant `boxScaling` of the box norm at the constant direction family
`[1,D]` and the window `symIcc L`. -/
lemma boxScaling_arithIcc (s D L : ℕ) :
    Work.Peluse.BoxNorm.boxScaling (s+1) (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D)
        (Work.Peluse.symIcc L)
      = (((2*L+1 : ℕ)) : ℝ)⁻¹ * ((D:ℝ)⁻¹)^(s+1) * ((D:ℝ)⁻¹)^(s+1) := by
  rw [Work.Peluse.BoxNorm.boxScaling, Work.Peluse.Ulower.card_symIcc]
  have h1 : (∏ i : Fin (s+1),
        (((fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) i).card : ℝ)⁻¹)
      = ((D:ℝ)⁻¹)^(s+1) := by
    simp only [Work.Peluse.Ulower.card_arithIcc_one]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1]

/-- The level-`(s+1)` box-norm power written through `normSqSum` for the constant direction family
`[1,D]`. -/
lemma boxNormPow_arithIcc_eq (s D L : ℕ) (f : ℤ → ℂ)
    (hsupp : Work.Peluse.SupportIn f (L + s * D)) :
    Work.Peluse.boxNormPow (s+1) (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D)
        (Work.Peluse.symIcc L) f
      = ((((2*L+1 : ℕ)) : ℝ)⁻¹ * ((D:ℝ)⁻¹)^(s+1) * ((D:ℝ)⁻¹)^(s+1))
        * Work.Peluse.BoxNorm.normSqSum (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) f
            (L + s * D) := by
  rw [Work.Peluse.LevelRaise.boxNormPow_succ_eq_scaling_mul_normSq _ _ f hsupp,
    boxScaling_arithIcc s D L]

/-! ## The aggregate window-sum bound -/

/-- **The aggregate window-sum bound.**  For `D ≥ 1` and `f` supported in `[-L,L]`, the average of
the squared norms of the level-`s` cube sums is bounded by the window-sum aggregate times the
elementary factor `(L⁻¹)² (2(L+sD+D)+1) D⁻²`. -/
lemma windowAggregate_aux (s L D : ℕ) (f : ℤ → ℂ) (hD : 1 ≤ D)
    (hsupp : Work.Peluse.SupportIn f L) :
    (∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
        ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2)
      ≤ ((L:ℝ)⁻¹)^2 * (2 * ((L + s*D + D : ℕ) : ℝ) + 1) * ((D:ℝ)⁻¹)^2
        * Work.Peluse.BoxNorm.normSqSum (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) f
            (L + s*D) := by
  classical
  have hWsum : (∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
        ∑' x : ℤ, ‖∑ a ∈ Work.Peluse.arithIcc 1 D,
            Work.Peluse.cubeTerm u v f (x + a)‖ ^ 2)
      = Work.Peluse.BoxNorm.normSqSum (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) f
          (L + s*D) := by
    rw [← windowSum_eq_normSqSum s D (L + s*D) f]
    refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => ?_))
    exact tsum_windowSq_eq_sum_ball hD hsupp
      (fun i => natAbs_le_of_mem_arithIcc (Fintype.mem_piFinset.mp hv i))
  have hZ : ∀ Z : ℂ, ‖((L : ℂ))⁻¹ * Z‖ ^ 2 = ((L:ℝ)⁻¹)^2 * ‖Z‖ ^ 2 := by
    intro Z
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    ring
  have hpair : ∀ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ∀ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ‖∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2
        ≤ (2 * ((L + s*D + D : ℕ) : ℝ) + 1) * ((D:ℝ)⁻¹)^2
          * ∑' x : ℤ, ‖∑ a ∈ Work.Peluse.arithIcc 1 D,
              Work.Peluse.cubeTerm u v f (x + a)‖ ^ 2 := by
    intro u hu v hv
    exact norm_tsum_sq_le_windowSum (D := D) (N := L + s*D) hD
      (Work.Peluse.cubeTerm u v f)
      (supportIn_cubeTerm (s := s) (L := L) (D := D) hsupp
        (fun i => natAbs_le_of_mem_arithIcc (Fintype.mem_piFinset.mp hv i)))
  calc
    (∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
        ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2)
      = ((L:ℝ)⁻¹)^2 * (∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
            ‖∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
          exact hZ _
    _ ≤ ((L:ℝ)⁻¹)^2 * ((2 * ((L + s*D + D : ℕ) : ℝ) + 1) * ((D:ℝ)⁻¹)^2
          * (∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
                ∑' x : ℤ, ‖∑ a ∈ Work.Peluse.arithIcc 1 D,
                    Work.Peluse.cubeTerm u v f (x + a)‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          simp only [Finset.mul_sum]
          exact Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => hpair u hu v hv))
    _ = ((L:ℝ)⁻¹)^2 * (2 * ((L + s*D + D : ℕ) : ℝ) + 1) * ((D:ℝ)⁻¹)^2
          * Work.Peluse.BoxNorm.normSqSum (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D) f
              (L + s*D) := by
          rw [← hWsum]; ring

/-- The arithmetic core: for `1 ≤ D ≤ L`, `(2L+1)(2(L+sD+D)+1) ≤ (6s+16)L²`. -/
lemma arith_key (s : ℕ) {L D : ℝ} (hL : 1 ≤ L) (hD : 1 ≤ D) (hDL : D ≤ L) :
    (2 * (L + (s:ℝ) * D + D) + 1) * (2 * L + 1) ≤ (6 * (s:ℝ) + 16) * L ^ 2 := by
  have hs0 : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
  have hL0 : (0:ℝ) ≤ L := by linarith [hL]
  have h1 : L + (s:ℝ) * D + D ≤ ((s:ℝ) + 2) * L := by nlinarith [hDL, hL, hs0]
  have h2 : 2 * (L + (s:ℝ) * D + D) + 1 ≤ (2 * (s:ℝ) + 5) * L := by nlinarith [h1, hL]
  have h3 : 2 * L + 1 ≤ 3 * L := by linarith [hL]
  have hA : (0:ℝ) ≤ 2 * L + 1 := by linarith [hL]
  have hB : (0:ℝ) ≤ (2 * (s:ℝ) + 5) * L :=
    mul_nonneg (by linarith [hs0]) hL0
  have h6 : ((2 * (s:ℝ) + 5) * L) * (3 * L) ≤ (6 * (s:ℝ) + 16) * L ^ 2 := by
    nlinarith [hL]
  calc (2 * (L + (s:ℝ) * D + D) + 1) * (2 * L + 1)
      ≤ ((2 * (s:ℝ) + 5) * L) * (2 * L + 1) := mul_le_mul_of_nonneg_right h2 hA
    _ ≤ ((2 * (s:ℝ) + 5) * L) * (3 * L) := mul_le_mul_of_nonneg_left h3 hB
    _ ≤ (6 * (s:ℝ) + 16) * L ^ 2 := h6

/-- **The window-aggregate bound** (the window-sum/Cauchy--Schwarz step of Peluse's Lemma 7.5). -/
theorem windowAggregate :
    ∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧
      ∀ (L D : ℕ) (f : ℤ → ℂ),
        1 ≤ L → 1 ≤ D → (D : ℝ) ≤ (L : ℝ) →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f L →
        C * (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
                ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2)
          ≤ Work.Peluse.boxNormPow (s + 1) (fun _ : Fin (s + 1) => Work.Peluse.arithIcc 1 D)
              (Work.Peluse.symIcc L) f := by
  intro s hs
  refine ⟨(1 : ℝ) / (6 * (s:ℝ) + 16), by positivity, ?_⟩
  intro L D f hL hD hDL hf hsupp
  rw [← arithIcc_one_eq D]
  have hpositive : (0:ℝ) < (1 : ℝ) / (6 * (s:ℝ) + 16) := by positivity
  have hCnn : (0:ℝ) ≤ (1 : ℝ) / (6 * (s:ℝ) + 16) := le_of_lt hpositive
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hden : (6 * (s:ℝ) + 16) ≠ 0 := by positivity
  have heenn : (0:ℝ) ≤ (D:ℝ)⁻¹ := by positivity
  have hsupportN : Work.Peluse.SupportIn f (L + s * D) :=
    Work.Peluse.SupportIn.mono hsupp (by omega)
  have hcast2L : (((2*L+1 : ℕ)) : ℝ) = 2*(L:ℝ)+1 := by push_cast; ring
  rw [boxNormPow_arithIcc_eq s D L f hsupportN, hcast2L]
  set NS : ℝ := Work.Peluse.BoxNorm.normSqSum (fun _ : Fin (s+1) => Work.Peluse.arithIcc 1 D)
      f (L + s*D) with hNS
  have hNSnn : (0:ℝ) ≤ NS := by
    rw [hNS]
    exact Work.Peluse.BoxNorm.normSqSum_nonneg _ _ _
  set ee : ℝ := (D:ℝ)⁻¹ with hee
  have heenn' : (0:ℝ) ≤ ee := by rw [hee]; exact heenn
  set ll : ℝ := (L:ℝ)⁻¹ with hll
  set KK : ℝ := 2 * ((L + s*D + D : ℕ) : ℝ) + 1 with hKK
  have haux := windowAggregate_aux s L D f hD hsupp
  rw [← hee, ← hll, ← hKK, ← hNS] at haux
  have hcard : ((Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)).card : ℝ)
      = (D:ℝ)^s := by
    rw [card_piFinset_arithIcc, Nat.cast_pow]
  have hc2 : ((Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹
        * ((Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹
      = ee^(2*s) := by
    rw [hcard, ← inv_pow, ← hee, ← pow_add]
    congr 1
    omega
  have hK1cast : ((L + s*D + D : ℕ) : ℝ) = (L:ℝ) + (s:ℝ)*(D:ℝ) + (D:ℝ) := by
    push_cast; ring
  have har : KK * (2*(L:ℝ)+1) ≤ (6*(s:ℝ)+16) * (L:ℝ)^2 := by
    rw [hKK, hK1cast]
    exact arith_key s (by exact_mod_cast hL) (by exact_mod_cast hD) hDL
  have hCL : (1 : ℝ)/(6*(s:ℝ)+16) * (6*(s:ℝ)+16) = 1 := by
    rw [one_div, inv_mul_cancel₀ hden]
  have hLl : ll^2 * (L:ℝ)^2 = 1 := by
    rw [hll, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hLpos), one_pow]
  have hkey : (1 : ℝ)/(6*(s:ℝ)+16) * (ll^2 * KK) * (2*(L:ℝ)+1) ≤ 1 := by
    have h1 : (0:ℝ) ≤ (1:ℝ)/(6*(s:ℝ)+16) * ll^2 := mul_nonneg hCnn (sq_nonneg ll)
    have h2 : (1:ℝ)/(6*(s:ℝ)+16) * ll^2 * (KK * (2*(L:ℝ)+1))
        ≤ (1:ℝ)/(6*(s:ℝ)+16) * ll^2 * ((6*(s:ℝ)+16) * (L:ℝ)^2) :=
      mul_le_mul_of_nonneg_left har h1
    have h3 : (1:ℝ)/(6*(s:ℝ)+16) * ll^2 * ((6*(s:ℝ)+16) * (L:ℝ)^2) = 1 := by
      rw [show (1:ℝ)/(6*(s:ℝ)+16) * ll^2 * ((6*(s:ℝ)+16) * (L:ℝ)^2)
            = ((1:ℝ)/(6*(s:ℝ)+16) * (6*(s:ℝ)+16)) * (ll^2 * (L:ℝ)^2) by ring,
          hCL, hLl, one_mul]
    calc (1:ℝ)/(6*(s:ℝ)+16) * (ll^2 * KK) * (2*(L:ℝ)+1)
        = (1:ℝ)/(6*(s:ℝ)+16) * ll^2 * (KK * (2*(L:ℝ)+1)) := by ring
      _ ≤ (1:ℝ)/(6*(s:ℝ)+16) * ll^2 * ((6*(s:ℝ)+16) * (L:ℝ)^2) := h2
      _ = 1 := h3
  have hkey' : (1:ℝ)/(6*(s:ℝ)+16) * (ll^2 * KK) ≤ (2*(L:ℝ)+1)⁻¹ := by
    have h2L1pos : (0:ℝ) < 2*(L:ℝ)+1 := by linarith [hL]
    calc (1:ℝ)/(6*(s:ℝ)+16) * (ll^2 * KK)
        = (1:ℝ)/(6*(s:ℝ)+16) * (ll^2 * KK) * ((2*(L:ℝ)+1) * (2*(L:ℝ)+1)⁻¹) := by
          rw [mul_inv_cancel₀ (ne_of_gt h2L1pos), mul_one]
      _ = ((1:ℝ)/(6*(s:ℝ)+16) * (ll^2 * KK) * (2*(L:ℝ)+1)) * (2*(L:ℝ)+1)⁻¹ := by ring
      _ ≤ 1 * (2*(L:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = (2*(L:ℝ)+1)⁻¹ := one_mul _
  calc (1 : ℝ) / (6 * (s:ℝ) + 16) *
        (((Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
          ((Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
          ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
            ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
              ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2)
      = (1 : ℝ) / (6 * (s:ℝ) + 16) *
          (ee^(2*s) * (∑ u ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
            ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
              ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2)) := by
          rw [hc2]
    _ ≤ (1 : ℝ) / (6 * (s:ℝ) + 16) * (ee^(2*s) * (ll^2 * KK * ee^2 * NS)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCnn
          exact mul_le_mul_of_nonneg_left haux (pow_nonneg heenn' (2*s))
    _ = ((1 : ℝ) / (6 * (s:ℝ) + 16) * (ll^2 * KK)) * ((ee^(s+1) * ee^(s+1)) * NS) := by
          rw [show ee^(2*s) * (ll^2 * KK * ee^2 * NS) = (ll^2*KK) * (ee^(2*s) * ee^2) * NS
                by ring,
              show ee^(2*s) * ee^2 = ee^(s+1) * ee^(s+1) by
                rw [← pow_add, ← pow_add]; congr 1; omega]
          ring
    _ ≤ (2*(L:ℝ)+1)⁻¹ * ((ee^(s+1) * ee^(s+1)) * NS) := by
          refine mul_le_mul_of_nonneg_right hkey' ?_
          exact mul_nonneg (mul_nonneg (pow_nonneg heenn' _) (pow_nonneg heenn' _)) hNSnn
    _ = (((2*(L:ℝ)+1)⁻¹ * ee^(s+1)) * ee^(s+1)) * NS := by ring

end

end Work.Peluse.Ulower
