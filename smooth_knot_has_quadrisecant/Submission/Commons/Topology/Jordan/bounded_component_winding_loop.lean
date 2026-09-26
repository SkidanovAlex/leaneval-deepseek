import Mathlib
import Submission.Commons.Topology.Jordan.bounded_gap_of_bounded_component
import Submission.Commons.Topology.Strip.barrier_bottom_top_of_no_left_right
import Submission.Commons.Topology.Strip.path_to_translate_of_open_cover_cancellation

open Set Complex
open scoped Topology

namespace Commons.Topology.Jordan

noncomputable section

/-!
# A bounded component of a closed subset of `ℂ` leaves a winding-once loop in the complement

**Target.** If `K ⊆ ℂ` is closed, `0 ∈ K`, and the connected component of `0` in `K` is bounded,
then there is a loop `γ : Circle → ℂ` avoiding `K` together with a continuous argument
`Θ : ℝ → ℝ` with `Θ (t + 2π) = Θ t + 2π` and `γ (exp t) = ‖γ (exp t)‖ * exp (I * Θ t)`;
equivalently (the classical statement) the complement of `K` contains a loop winding once
around `0`.

**Proof structure of the present file.**  Let `D ⊆ K` be the bounded closed set and `δ > 0` the
uniform gap produced by `bounded_gap_of_bounded_component`, so that `K ∩ {z | infDist z D < δ} = D`.
Then `D` is *clopen* in `K`, `K \ D` is closed, and

* every ray from `0` leaves `D` and stays at distance `< δ` from `D` for a whole interval after
  its last point in `D` (so the ray is free there);
* no preconnected subset of `L := K ∩ {δ/2 ≤ ‖·‖ ≤ R}` meets both boundary circles
  (`hjoin` below): this is the elementary `infDist`-argument, valid because a point of `K` of
  norm `δ/2` lies in `D` while one of norm `R > sup ‖·‖|_D` does not.

Next, `K` is split in the strip model of the annulus into

  `A := {q | cov q ∈ K \ D, r ≤ q.2 ≤ R}`,   `B := {q | cov q ∈ D, r ≤ q.2 ≤ R}`

(`cov (x,y) = y * exp (x * I)` is the log-polar cover).  Both are closed, `p`-periodic
(`p = 2π`), disjoint, and `A` avoids the bottom line `q.2 = r` while `B` avoids the top line
`q.2 = R`.

The single remaining input is the planar core `periodic_path_of_split` (Denne,
*Alternating quadrisecants of knots*, Prop. 25): a closed `p`-periodic set in the strip that
splits into a part avoiding the bottom boundary line and a part avoiding the top boundary line
leaves a *translate-path* in the complement.  From such a path `G` the required loop is
`c ↦ cov (G t)` (with `c = exp t`) and the required argument is `Θ = G.1`.

## On the core statement

`periodic_path_of_split` is *not* a formal triviality: the corresponding statement for a single
closed set (without the splitting) is **false** (`Submission/Work/Topology/Strip/…`;
the "spiral tower" counterexample), and the splitting is exactly what the geometric hypotheses
of this file provide.  The natural route to the core is: (i) upgrade the pointwise boundary
hypotheses `hAbot`/`hBtop` to uniform margins `A ⊆ {q.2 ≥ a + ε}`, `B ⊆ {q.2 ≤ b - δ}` (closed +
periodic + compact fundamental domain); (ii) apply the barrier lemma
`Commons.Topology.Strip.barrier_bottom_top_of_no_left_right` in the shrunk boxes
`[0,p] × [a, b - t]` to get left–right crossings avoiding `A ∪ B` (the hypotheses of the barrier
lemma hold because a preconnected `C ⊆ (A ∪ B) ∩ box` lies in `A` or in `B`, hence cannot meet
both horizontal lines); (iii) upgrade a crossing to an equal-height crossing via the
"open-cover cancellation" `path_to_translate_of_open_cover_cancellation` (Step (iii) is the
remaining gap). -/

/-! ## The log-polar cover

`cov q = q.2 * exp (q.1 * I)` is the (partially defined) universal cover of the punctured
plane: `cov` is `2π`-periodic in the first coordinate and `‖cov q‖ = |q.2|`.
-/
def cov (q : ℝ × ℝ) : ℂ := (q.2 : ℂ) * Complex.exp ((q.1 : ℂ) * Complex.I)

lemma cov_add_two_pi (q : ℝ × ℝ) : cov (q.1 + 2 * Real.pi, q.2) = cov q := by
  unfold cov
  have h : (((q.1 + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
      = (q.1 : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma norm_cov (q : ℝ × ℝ) : ‖cov q‖ = |q.2| := by
  have hre : (((q.1 : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  unfold cov
  rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

lemma cov_ne_zero_iff {q : ℝ × ℝ} : cov q ≠ 0 ↔ q.2 ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_cov, abs_ne_zero]

lemma continuous_cov : Continuous cov := by unfold cov; fun_prop

/-- `cov` is invariant under integer shifts of the first coordinate by `2π`. -/
lemma cov_add_int (m : ℤ) (q : ℝ × ℝ) :
    cov (q.1 + m * (2 * Real.pi), q.2) = cov q := by
  unfold cov
  have h : (((q.1 + m * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I
      = (q.1 : ℂ) * Complex.I + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
  simp

/-! ## The building blocks of the core

The two ingredients below are standard and elementary: the pointwise boundary hypotheses of the
splitting upgrade to *uniform* margins (closedness + periodicity + a compact fundamental domain),
and membership in the periodic set is unchanged by integer shifts of the first coordinate. -/

/-- Membership in a `p`-periodic set is unchanged by integer multiples of `p`. -/
theorem mem_add_intCast_mul {p : ℝ} {A : Set (ℝ × ℝ)}
    (hAper : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A) (m : ℤ) (q : ℝ × ℝ) :
    q ∈ A ↔ (q.1 + p * (m : ℝ), q.2) ∈ A := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hpt : q.1 + p * (((k : ℤ) + 1 : ℤ) : ℝ) = (q.1 + p * (k : ℝ)) + p := by
        push_cast; ring
      rw [hpt, ← hAper (q.1 + p * (↑k : ℝ), q.2)]
      exact ih
  | pred k ih =>
      have hpt : q.1 + p * ((-(k : ℤ) - 1 : ℤ) : ℝ) = (q.1 + p * (-(k : ℝ))) - p := by
        push_cast; ring
      have h3 : (q.1 + p * (-(k : ℝ))) - p + p = q.1 + p * (-(k : ℝ)) := by ring
      have h2 : ((q.1 + p * (-(k : ℝ))) - p, q.2) ∈ A ↔ (q.1 + p * (-(k : ℝ)), q.2) ∈ A := by
        have h := hAper ((q.1 + p * (-(k : ℝ))) - p, q.2)
        simpa [h3] using h
      rw [hpt, h2]
      simpa using ih

/-- Some integer translate of a real number lands in `[0, p]`. -/
theorem exists_add_mul_mem_Icc {p x : ℝ} (hp : 0 < p) :
    ∃ m : ℤ, x + p * (m : ℝ) ∈ Set.Icc (0 : ℝ) p := by
  refine ⟨-(⌊x / p⌋), ?_⟩
  have hsplit : x / p - (⌊x / p⌋ : ℝ) = Int.fract (x / p) := (Int.self_sub_floor _).symm
  have hval : x + p * ((-(⌊x / p⌋) : ℤ) : ℝ) = p * Int.fract (x / p) := by
    rw [Int.cast_neg, ← hsplit]
    field_simp
    ring
  rw [hval]
  refine ⟨mul_nonneg hp.le (Int.fract_nonneg _), ?_⟩
  have hlt := Int.fract_lt_one (x / p)
  nlinarith [hlt, hp]

/-- **Uniform margin at the bottom.**  A closed `p`-periodic set inside the strip that meets no
point of the bottom line `q.2 = a` in fact stays at distance `≥ ε > 0` from it. -/
theorem exists_add_eps_le_snd_of_closed_periodic_gt {p a b : ℝ} (hp : 0 < p) {A : Set (ℝ × ℝ)}
    (hA : IsClosed A) (hAsub : A ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hAper : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A)
    (hAbot : ∀ q ∈ A, a < q.2) :
    ∃ ε : ℝ, 0 < ε ∧ A ⊆ {q : ℝ × ℝ | a + ε ≤ q.2} := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun q hq => absurd hq (Set.notMem_empty q)⟩
  set S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) p ×ˢ Set.Icc a b with hS
  have hScompact : IsCompact S := by
    rw [hS]; exact isCompact_Icc.prod isCompact_Icc
  have hKcompact : IsCompact (A ∩ S) :=
    hScompact.of_isClosed_subset (hA.inter hScompact.isClosed) Set.inter_subset_right
  have hKne : (A ∩ S).Nonempty := by
    obtain ⟨q₁, hq₁⟩ := hne
    obtain ⟨m, hm⟩ := exists_add_mul_mem_Icc (p := p) hp (x := q₁.1)
    refine ⟨(q₁.1 + p * (m : ℝ), q₁.2), ?_, ?_⟩
    · exact (mem_add_intCast_mul hAper m q₁).mp hq₁
    · exact ⟨hm, (hAsub hq₁).1, (hAsub hq₁).2⟩
  obtain ⟨q₀, hq₀K, hq₀min⟩ := hKcompact.exists_isMinOn hKne continuous_snd.continuousOn
  refine ⟨q₀.2 - a, ?_, ?_⟩
  · linarith [hAbot q₀ hq₀K.1]
  · intro q hq
    obtain ⟨m, hm⟩ := exists_add_mul_mem_Icc (p := p) hp (x := q.1)
    have hq' : (q.1 + p * (m : ℝ), q.2) ∈ A := (mem_add_intCast_mul hAper m q).mp hq
    have hsub := hAsub hq
    have hmem : (q.1 + p * (m : ℝ), q.2) ∈ A ∩ S := ⟨hq', hm, hsub⟩
    have hle : q₀.2 ≤ q.2 := by simpa using hq₀min hmem
    show a + (q₀.2 - a) ≤ q.2
    linarith

/-- **Uniform margin at the top.**  A closed `p`-periodic set inside the strip that meets no
point of the top line `q.2 = b` in fact stays at distance `≥ δ > 0` from it. -/
theorem exists_snd_le_sub_of_closed_periodic_lt {p a b : ℝ} (hp : 0 < p) {B : Set (ℝ × ℝ)}
    (hB : IsClosed B) (hBsub : B ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hBper : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B)
    (hBtop : ∀ q ∈ B, q.2 < b) :
    ∃ δ : ℝ, 0 < δ ∧ B ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ} := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun q hq => absurd hq (Set.notMem_empty q)⟩
  set S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) p ×ˢ Set.Icc a b with hS
  have hScompact : IsCompact S := by
    rw [hS]; exact isCompact_Icc.prod isCompact_Icc
  have hKcompact : IsCompact (B ∩ S) :=
    hScompact.of_isClosed_subset (hB.inter hScompact.isClosed) Set.inter_subset_right
  have hKne : (B ∩ S).Nonempty := by
    obtain ⟨q₁, hq₁⟩ := hne
    obtain ⟨m, hm⟩ := exists_add_mul_mem_Icc (p := p) hp (x := q₁.1)
    refine ⟨(q₁.1 + p * (m : ℝ), q₁.2), ?_, ?_⟩
    · exact (mem_add_intCast_mul hBper m q₁).mp hq₁
    · exact ⟨hm, (hBsub hq₁).1, (hBsub hq₁).2⟩
  obtain ⟨q₀, hq₀K, hq₀max⟩ := hKcompact.exists_isMaxOn hKne continuous_snd.continuousOn
  refine ⟨b - q₀.2, ?_, ?_⟩
  · linarith [hBtop q₀ hq₀K.1]
  · intro q hq
    obtain ⟨m, hm⟩ := exists_add_mul_mem_Icc (p := p) hp (x := q.1)
    have hq' : (q.1 + p * (m : ℝ), q.2) ∈ B := (mem_add_intCast_mul hBper m q).mp hq
    have hsub := hBsub hq
    have hmem : (q.1 + p * (m : ℝ), q.2) ∈ B ∩ S := ⟨hq', hm, hsub⟩
    have hle : q.2 ≤ q₀.2 := by simpa using hq₀max hmem
    show q.2 ≤ b - (b - q₀.2)
    linarith

/-! ## Unrolling a translate-path to a `ℝ`-map

A path `γ : [0,1] → ℝ × ℝ` with `γ 1 = γ 0 + (p, 0)` extends uniquely to a continuous
`G : ℝ → ℝ × ℝ` with `G (t + p) = ((G t).1 + p, (G t).2)`, by gluing the translates of `γ`. -/

/-- The representative of `s` in `[0,1)` as an element of `I`. -/
def fI (s : ℝ) : Set.Icc (0:ℝ) 1 :=
  ⟨Int.fract s, Int.fract_nonneg s, (Int.fract_lt_one s).le⟩

@[simp] lemma fI_val (s : ℝ) : (fI s : ℝ) = Int.fract s := rfl

lemma fI_add_one (s : ℝ) : fI (s + 1) = fI s := by
  apply Subtype.ext
  simp only [fI_val]
  exact Int.fract_add_one s

/-- The unit-period unrolling. -/
noncomputable def unrollUnit (p : ℝ) (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (u : ℝ) : ℝ × ℝ :=
  γ (fI u) + (((⌊u⌋ : ℤ) : ℝ) * p, 0)

lemma unrollUnit_eq_of_mem {p : ℝ} {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} {n : ℤ} {u : ℝ}
    (hu : u ∈ Set.Ico (n:ℝ) ((n:ℝ)+1)) :
    unrollUnit p γ u
      = γ ⟨u - (n:ℝ), by have := hu.1; linarith, by have := hu.2; linarith⟩
        + (((n : ℝ) * p), 0) := by
  have hfl : ⌊u⌋ = n := Int.floor_eq_on_Ico n u hu
  have hfr : fI u = ⟨u - (n:ℝ), by have := hu.1; linarith, by have := hu.2; linarith⟩ := by
    apply Subtype.ext
    simp only [fI_val]
    rw [← Int.self_sub_floor, hfl]
  unfold unrollUnit
  rw [hfr, hfl]

lemma unrollUnit_eq_of_mem_Icc {p : ℝ} {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hγ : γ 1 = γ 0 + (p, 0)) {n : ℤ} {u : ℝ} (hu : u ∈ Set.Icc (n:ℝ) ((n:ℝ)+1)) :
    unrollUnit p γ u
      = γ ⟨u - (n:ℝ), by have := hu.1; linarith, by have := hu.2; linarith⟩
        + (((n : ℝ) * p), 0) := by
  rcases lt_or_eq_of_le hu.2 with hlt | heq
  · exact unrollUnit_eq_of_mem (p := p) (γ := γ) (n := n) (u := u) ⟨hu.1, hlt⟩
  · subst heq
    have hval : unrollUnit p γ ((n:ℝ) + 1) = γ 0 + (((n:ℝ) + 1) * p, 0) := by
      unfold unrollUnit
      rw [show fI ((n:ℝ) + 1) = (0 : Set.Icc (0:ℝ) 1) from by
        rw [fI_add_one]
        apply Subtype.ext
        simp only [fI_val, Int.fract_intCast]
        rfl]
      rw [show ⌊(n:ℝ) + 1⌋ = n + 1 from by rw [Int.floor_add_one, Int.floor_intCast]]
      simp only [Int.cast_add, Int.cast_one]
    rw [hval]
    have hsub : (⟨(n:ℝ) + 1 - (n:ℝ), by linarith, by linarith⟩ : Set.Icc (0:ℝ) 1) = 1 := by
      apply Subtype.ext; simp
    rw [hsub, hγ]
    refine Prod.ext ?_ ?_ <;> simp <;> ring

lemma unrollUnit_continuousOn {p : ℝ} (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (n : ℤ) :
    ContinuousOn (unrollUnit p γ) (Set.Ico (n : ℝ) ((n : ℝ) + 1)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hcont : Continuous fun u : ↥(Set.Ico (n:ℝ) ((n:ℝ)+1)) =>
      γ ⟨(u:ℝ) - (n:ℝ), by have := u.2.1; linarith, by have := u.2.2; linarith⟩
        + (((n : ℝ) * p), 0) := by
    refine Continuous.add ?_ continuous_const
    refine γ.continuous.comp ?_
    exact Continuous.subtype_mk (continuous_subtype_val.sub continuous_const) _
  exact hcont.congr (fun u => (unrollUnit_eq_of_mem u.2).symm)

lemma unrollUnit_continuousOn_Icc {p : ℝ} {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hγ : γ 1 = γ 0 + (p, 0)) (n : ℤ) :
    ContinuousOn (unrollUnit p γ) (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hcont : Continuous fun u : ↥(Set.Icc (n:ℝ) ((n:ℝ)+1)) =>
      γ ⟨(u:ℝ) - (n:ℝ), by have := u.2.1; linarith, by have := u.2.2; linarith⟩
        + (((n : ℝ) * p), 0) := by
    refine Continuous.add ?_ continuous_const
    refine γ.continuous.comp ?_
    exact Continuous.subtype_mk (continuous_subtype_val.sub continuous_const) _
  exact hcont.congr (fun u => (unrollUnit_eq_of_mem_Icc hγ u.2).symm)

lemma unrollUnit_continuous {p : ℝ} (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ))
    (hγ : γ 1 = γ 0 + (p, 0)) : Continuous (unrollUnit p γ) := by
  refine continuous_of_cover_nhds (s := fun m : ℤ => Set.Ioo ((m:ℝ) - 2/3) ((m:ℝ) + 2/3)) ?_ ?_
  · intro x
    refine ⟨⌊x + 1/2⌋, ?_⟩
    have h1 : ((⌊x + 1/2⌋ : ℤ) : ℝ) ≤ x + 1/2 := Int.floor_le _
    have h2 : x + 1/2 < ((⌊x + 1/2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    exact Filter.mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) (fun y hy => hy)
  · intro m
    have hcast1 : (((m-1 : ℤ) : ℝ)) = (m:ℝ) - 1 := by push_cast; ring
    have hcast2 : (((m+1 : ℤ) : ℝ)) = (m:ℝ) + 1 := by push_cast; ring
    have hsub : Set.Ioo ((m:ℝ) - 2/3) ((m:ℝ) + 2/3) ⊆
        Set.Icc (((m-1 : ℤ) : ℝ)) (m:ℝ) ∪ Set.Icc (m:ℝ) (((m+1 : ℤ) : ℝ)) := by
      intro u hu
      rw [Set.mem_Ioo] at hu
      rw [hcast1, hcast2]
      rcases le_total u (m:ℝ) with h | h
      · exact Or.inl ⟨by linarith [hu.1], h⟩
      · exact Or.inr ⟨h, by linarith [hu.2]⟩
    have hc1 : ContinuousOn (unrollUnit p γ) (Set.Icc (((m-1 : ℤ) : ℝ)) (m:ℝ)) := by
      have := unrollUnit_continuousOn_Icc (p := p) hγ (m-1)
      rwa [show (((m-1 : ℤ) : ℝ)) + 1 = (m:ℝ) from by push_cast; ring] at this
    have hc2 : ContinuousOn (unrollUnit p γ) (Set.Icc (m:ℝ) (((m+1 : ℤ) : ℝ))) := by
      have := unrollUnit_continuousOn_Icc (p := p) hγ m
      rwa [show (((m : ℤ) : ℝ)) + 1 = (((m+1 : ℤ) : ℝ)) from by push_cast; ring] at this
    exact ((hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).mono hsub)

lemma unrollUnit_add_one {p : ℝ} (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (u : ℝ) :
    unrollUnit p γ (u + 1) = unrollUnit p γ u + ((p : ℝ), 0) := by
  unfold unrollUnit
  rw [fI_add_one, Int.floor_add_one]
  simp only [Int.cast_add, Int.cast_one]
  ext <;> simp <;> ring

/-- The unrolling of a path with `γ 1 = γ 0 + (p, 0)`. -/
noncomputable def unroll (p : ℝ) (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (s : ℝ) : ℝ × ℝ :=
  unrollUnit p γ (s / p)

lemma unroll_continuous {p : ℝ} (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ))
    (hγ : γ 1 = γ 0 + (p, 0)) : Continuous (unroll p γ) :=
  (unrollUnit_continuous γ hγ).comp (continuous_id.div_const p)

lemma unroll_period {p : ℝ} (hp : 0 < p) (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ))
    (hγ : γ 1 = γ 0 + (p, 0)) (s : ℝ) :
    unroll p γ (s + p) = unroll p γ s + ((p : ℝ), 0) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hdiv : (s + p) / p = s / p + 1 := by rw [add_div, div_self hp0]
  unfold unroll
  rw [hdiv]
  exact unrollUnit_add_one γ (s / p)

lemma unroll_zero {p : ℝ} (hp : 0 < p) (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) :
    unroll p γ 0 = γ 0 := by
  have h0 : (0:ℝ) / p = 0 := by simp
  have hf0 : fI (0:ℝ) = 0 := by
    apply Subtype.ext
    simp only [fI_val, Int.fract_zero]
    rfl
  unfold unroll
  rw [h0]
  unfold unrollUnit
  rw [hf0]
  simp

/-! ## The crux

This is the planar-core statement (Denne, *Alternating quadrisecants of knots*, Prop. 25, in the
periodic strip model): a closed `p`-periodic set in the strip that splits into a part avoiding the
bottom boundary line and a part avoiding the top boundary line leaves a translate-path in the
complement. -/
theorem periodic_path_of_split {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {A B : Set (ℝ × ℝ)} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B)
    (hAper : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A)
    (hBper : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B)
    (hAsub : A ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hBsub : B ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hAbot : ∀ q ∈ A, a < q.2) (hBtop : ∀ q ∈ B, q.2 < b) :
    ∃ G : C(ℝ, ℝ × ℝ), (∀ t, a ≤ (G t).2 ∧ (G t).2 ≤ b) ∧
      (∀ t, G (t + p) = ((G t).1 + p, (G t).2)) ∧ ∀ t, G t ∉ A ∪ B := by
  obtain ⟨ε, hεpos, hAeps⟩ :=
    exists_add_eps_le_snd_of_closed_periodic_gt hp hA hAsub hAper hAbot
  obtain ⟨δ, hδpos, hBdel⟩ :=
    exists_snd_le_sub_of_closed_periodic_lt hp hB hBsub hBper hBtop
  set ε' : ℝ := min ε ((b - a) / 2) with hε'
  set δ' : ℝ := min δ ((b - a) / 2) with hδ'
  have hε'pos : 0 < ε' := lt_min hεpos (by linarith)
  have hδ'pos : 0 < δ' := lt_min hδpos (by linarith)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hε'lt : ε' < b - a := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hδ'lt : δ' < b - a := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set O : Set (ℝ × ℝ) := {q : ℝ × ℝ | a < q.2 ∧ q.2 < b} with hO
  have hOopen : IsOpen O := by
    rw [hO]
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  set VA : Set (ℝ × ℝ) := O \ A with hVA
  set VB : Set (ℝ × ℝ) := O \ B with hVB
  have hVAopen : IsOpen VA := hOopen.sdiff hA
  have hVBopen : IsOpen VB := hOopen.sdiff hB
  have hsubA : VA ⊆ O := sdiff_subset
  have hsubB : VB ⊆ O := sdiff_subset
  have hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA := by
    intro q
    simp only [hVA, hO, mem_sdiff, mem_ofPred_eq]
    rw [hAper q]
  have hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB := by
    intro q
    simp only [hVB, hO, mem_sdiff, mem_ofPred_eq]
    rw [hBper q]
  have hcover : VA ∪ VB = O := by
    rw [hVA, hVB]
    ext q
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
    · intro hq
      by_cases hqA : q ∈ A
      · exact Or.inr ⟨hq, fun hqB => Set.disjoint_left.mp hdisj hqA hqB⟩
      · exact Or.inl ⟨hq, hqA⟩
  have hwindA : ∃ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ VA) ∧ (γ 0).2 = (γ 1).2 ∧ γ 1 = ((γ 0).1 + p, (γ 0).2) := by
    refine ⟨⟨fun t : Set.Icc (0:ℝ) 1 => ((t:ℝ) * p, a + ε' / 2), by fun_prop⟩, ?_, ?_, ?_⟩
    · intro t
      simp only [hVA, hO, mem_sdiff, mem_ofPred_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show a < a + ε' / 2
        linarith
      · show a + ε' / 2 < b
        linarith
      · intro hmem
        have h2 : a + ε ≤ (a + ε' / 2) := hAeps hmem
        have h3 : ε' / 2 < ε := by linarith
        linarith
    · show a + ε' / 2 = a + ε' / 2
      rfl
    · show (((1:Set.Icc (0:ℝ) 1):ℝ) * p, a + ε' / 2)
          = ((((0:Set.Icc (0:ℝ) 1):ℝ) * p) + p, a + ε' / 2)
      simp
  have hwindB : ∃ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ VB) ∧ (γ 0).2 = (γ 1).2 ∧ γ 0 = ((γ 1).1 + p, (γ 1).2) := by
    refine ⟨⟨fun t : Set.Icc (0:ℝ) 1 => (p * (1 - (t:ℝ)), b - δ' / 2), by fun_prop⟩, ?_, ?_, ?_⟩
    · intro t
      simp only [hVB, hO, mem_sdiff, mem_ofPred_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show a < b - δ' / 2
        linarith
      · show b - δ' / 2 < b
        linarith
      · intro hmem
        have h2 : b - δ' / 2 ≤ b - δ := hBdel hmem
        have h3 : δ' / 2 < δ := by linarith
        linarith
    · show b - δ' / 2 = b - δ' / 2
      rfl
    · show (p * (1 - ((0:Set.Icc (0:ℝ) 1):ℝ)), b - δ' / 2)
          = ((p * (1 - ((1:Set.Icc (0:ℝ) 1):ℝ))) + p, b - δ' / 2)
      simp
  obtain ⟨z, _hz1, _hz2, _hzV, γ, hγ0, hγ1, hγV⟩ :=
    Commons.Topology.Strip.path_to_translate_of_open_cover_cancellation hp hab hVAopen hVBopen
      hsubA hsubB hperA hperB hcover hwindA hwindB
  have hγper : γ 1 = γ 0 + (p, 0) := by
    rw [hγ0, hγ1]
    ext <;> simp
  have hunroll : ∀ t, unroll p γ t = ((γ (fI (t / p))).1 + p * ((⌊t / p⌋ : ℤ) : ℝ),
      (γ (fI (t / p))).2) := by
    intro t
    unfold unroll unrollUnit
    ext <;> simp <;> ring
  refine ⟨⟨unroll p γ, unroll_continuous γ hγper⟩, ?_, ?_, ?_⟩
  · intro t
    have hbase : γ (fI (t / p)) ∈ VA ∩ VB := hγV _
    have hmem : unroll p γ t ∈ VA ∩ VB := by
      rw [hunroll t]
      exact ⟨(mem_add_intCast_mul hperA ⌊t / p⌋ _).mp hbase.1,
        (mem_add_intCast_mul hperB ⌊t / p⌋ _).mp hbase.2⟩
    have hO' : unroll p γ t ∈ O := hsubA hmem.1
    simp only [hO, mem_ofPred_eq] at hO'
    exact ⟨le_of_lt hO'.1, le_of_lt hO'.2⟩
  · intro t
    have h := unroll_period hp γ hγper t
    ext <;> simp [h]
  · intro t
    have hbase : γ (fI (t / p)) ∈ VA ∩ VB := hγV _
    have hmem : unroll p γ t ∈ VA ∩ VB := by
      rw [hunroll t]
      exact ⟨(mem_add_intCast_mul hperA ⌊t / p⌋ _).mp hbase.1,
        (mem_add_intCast_mul hperB ⌊t / p⌋ _).mp hbase.2⟩
    intro hcon
    rw [hVA] at hmem
    rw [hVB] at hmem
    rcases hcon with h | h
    · exact hmem.1.2 h
    · exact hmem.2.2 h

/-! ## From a periodic path in the log-polar cover to the required loop

Given a `2π`-periodic path `G` in the log-polar model of `ℂ*` that stays in the open half plane
`q.2 > 0` and avoids the lifted set `cov⁻¹ K`, the composite `t ↦ cov (G t)` descends to the
circle (`cov` is `2π`-periodic in the first coordinate) and its first coordinate `(G ·).1` is the
required continuous argument. -/

lemma periodic_path_per_nat (G : C(ℝ, ℝ × ℝ))
    (hper : ∀ t, G (t + 2 * Real.pi) = ((G t).1 + 2 * Real.pi, (G t).2)) :
    ∀ (k : ℕ) (t : ℝ), G (t + k * (2 * Real.pi)) = ((G t).1 + k * (2 * Real.pi), (G t).2) := by
  intro k
  induction k with
  | zero => intro t; simp
  | succ n ih =>
      intro t
      have h1 : t + (↑(n + 1) : ℝ) * (2 * Real.pi)
          = (t + ↑n * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
      rw [h1, hper, ih]
      congr 1
      push_cast; ring

lemma periodic_path_per_nat_neg (G : C(ℝ, ℝ × ℝ))
    (hper : ∀ t, G (t + 2 * Real.pi) = ((G t).1 + 2 * Real.pi, (G t).2)) :
    ∀ (k : ℕ) (t : ℝ), G (t - k * (2 * Real.pi)) = ((G t).1 - k * (2 * Real.pi), (G t).2) := by
  have hb : ∀ s : ℝ, G (s - 2 * Real.pi) = ((G s).1 - 2 * Real.pi, (G s).2) := by
    intro s
    have h := hper (s - 2 * Real.pi)
    rw [show s - 2 * Real.pi + 2 * Real.pi = s from by ring] at h
    rw [h]; simp
  intro k
  induction k with
  | zero => intro t; simp
  | succ n ih =>
      intro t
      have h1 : t - (↑(n + 1) : ℝ) * (2 * Real.pi) = (t - ↑n * (2 * Real.pi)) - 2 * Real.pi := by
        push_cast; ring
      rw [h1, hb, ih]
      congr 1
      push_cast; ring

lemma periodic_path_per_int (G : C(ℝ, ℝ × ℝ))
    (hper : ∀ t, G (t + 2 * Real.pi) = ((G t).1 + 2 * Real.pi, (G t).2)) :
    ∀ (m : ℤ) (t : ℝ), G (t + m * (2 * Real.pi)) = ((G t).1 + m * (2 * Real.pi), (G t).2) := by
  intro m t
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · subst hk; simpa using periodic_path_per_nat G hper k t
  · subst hk
    rw [show t + ((↑(-↑k) : ℤ) : ℝ) * (2 * Real.pi) = t - (k : ℝ) * (2 * Real.pi) by
      push_cast; ring]
    rw [show (G t).1 + ((↑(-↑k) : ℤ) : ℝ) * (2 * Real.pi)
        = (G t).1 - (k : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact periodic_path_per_nat_neg G hper k t

/-- **From a periodic path in the log-polar cover, build the required loop and argument.** -/
theorem exists_loop_arg_of_periodic_path (G : C(ℝ, ℝ × ℝ))
    (hpos : ∀ t, 0 < (G t).2)
    (hper : ∀ t, G (t + 2 * Real.pi) = ((G t).1 + 2 * Real.pi, (G t).2)) :
    ∃ γ : C(Circle, ℂ), (∀ t, γ (Circle.exp t) = cov (G t)) ∧
      ∃ Θ : C(ℝ, ℝ), (∀ t, Θ (t + 2 * Real.pi) = Θ t + 2 * Real.pi) ∧
        ∀ t, γ (Circle.exp t) = ((‖γ (Circle.exp t)‖ : ℝ) : ℂ)
          * Complex.exp ((Θ t : ℂ) * Complex.I) := by
  have hfac : Function.FactorsThrough (fun t : ℝ => cov (G t)) Circle.exp := by
    intro s t hst
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hst
    change cov (G s) = cov (G t)
    rw [hm, periodic_path_per_int G hper m t, cov_add_int m (G t)]
  have hq : Topology.IsQuotientMap ⇑Circle.exp :=
    Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective
  let γ : C(Circle, ℂ) := hq.lift ⟨fun t => cov (G t), continuous_cov.comp G.continuous⟩ hfac
  have hγ : ∀ t, γ (Circle.exp t) = cov (G t) := by
    intro t
    have hcomp : γ.comp Circle.exp
        = ⟨fun t => cov (G t), continuous_cov.comp G.continuous⟩ := hq.lift_comp _ hfac
    exact congr_fun (congrArg DFunLike.coe hcomp) t
  refine ⟨γ, hγ, ⟨⟨fun t => (G t).1, by fun_prop⟩, ?_, ?_⟩⟩
  · intro t; exact congrArg Prod.fst (hper t)
  · intro t
    rw [hγ t]
    show cov (G t) = ((‖cov (G t)‖ : ℝ) : ℂ) * Complex.exp (((G t).1 : ℂ) * Complex.I)
    rw [norm_cov, abs_of_pos (hpos t)]
    unfold cov
    rfl

/-! ## The periodic path from a bounded component -/

/-- **A periodic path in the log-polar cover avoiding the lifted set.**  From the bounded closed
set `D ⊆ K` with uniform gap `δ` of `bounded_gap_of_bounded_component`, split
`K ∩ {δ/2 ≤ ‖·‖ ≤ R}` into the closed `2π`-periodic pieces `K \ D` (which stays away from the
inner circle `‖·‖ = δ/2`, since a point of `K` that close to `D` would already be in `D`) and
`D` (which stays away from the outer circle `‖·‖ = R`, since `D` lies in a ball of radius `R`).
Applying `periodic_path_of_split` to the two lifted pieces yields the desired path. -/
theorem periodic_path_of_bounded_component {K : Set ℂ} (hK : IsClosed K) (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ G : C(ℝ, ℝ × ℝ), (∀ t, 0 < (G t).2) ∧
      (∀ t, cov (G t) ∉ K) ∧
      (∀ t, G (t + 2 * Real.pi) = ((G t).1 + 2 * Real.pi, (G t).2)) := by
  obtain ⟨D, hDclosed, hDbdd, hDK, h0D, δ, hδpos, hgap⟩ :=
    bounded_gap_of_bounded_component hK h0 hbdd
  obtain ⟨Cb, hCb⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hDbdd
  have hCb' : ∀ z ∈ D, ‖z‖ < Cb := by
    intro z hz
    have h := hCb hz
    rwa [Metric.mem_ball, dist_zero_right] at h
  -- `K \ D` is closed: it is the part of `K` at distance at least `δ` from `D`.
  have hKDclosed : IsClosed (K \ D) := by
    have heq : K \ D = K ∩ {z : ℂ | δ ≤ Metric.infDist z D} := by
      ext z
      rw [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hz
        exact ⟨hz.1, not_lt.mp fun hlt => hz.2 (hgap z hz.1 hlt)⟩
      · rintro ⟨hzK, hzδ⟩
        refine ⟨hzK, fun hzD => ?_⟩
        have hzero : Metric.infDist z D = 0 := by
          refine le_antisymm ?_ Metric.infDist_nonneg
          have h := Metric.infDist_le_dist_of_mem (x := z) hzD
          simpa using h
        linarith
    rw [heq]
    exact hK.inter (isClosed_le continuous_const (Metric.continuous_infDist_pt D))
  set r : ℝ := δ / 2 with hr
  set Rb : ℝ := max Cb r + 1 with hRb
  have hrpos : 0 < r := by rw [hr]; linarith
  have hδr : r < δ := by rw [hr]; linarith
  have hrRb : r < Rb := by rw [hRb]; linarith [le_max_right Cb r]
  have hCbRb : Cb < Rb := by rw [hRb]; linarith [le_max_left Cb r]
  set A : Set (ℝ × ℝ) := {q : ℝ × ℝ | cov q ∈ K \ D ∧ r ≤ q.2 ∧ q.2 ≤ Rb} with hA
  set B : Set (ℝ × ℝ) := {q : ℝ × ℝ | cov q ∈ D ∧ r ≤ q.2 ∧ q.2 ≤ Rb} with hB
  have hAclosed : IsClosed A := by
    have h1 : IsClosed {q : ℝ × ℝ | cov q ∈ K \ D} := hKDclosed.preimage continuous_cov
    have h2 : IsClosed {q : ℝ × ℝ | r ≤ q.2 ∧ q.2 ≤ Rb} :=
      (isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd continuous_const)
    have heq : A = {q : ℝ × ℝ | cov q ∈ K \ D} ∩ {q : ℝ × ℝ | r ≤ q.2 ∧ q.2 ≤ Rb} := by
      ext q; simp only [hA, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [heq]; exact h1.inter h2
  have hBclosed : IsClosed B := by
    have h1 : IsClosed {q : ℝ × ℝ | cov q ∈ D} := hDclosed.preimage continuous_cov
    have h2 : IsClosed {q : ℝ × ℝ | r ≤ q.2 ∧ q.2 ≤ Rb} :=
      (isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd continuous_const)
    have heq : B = {q : ℝ × ℝ | cov q ∈ D} ∩ {q : ℝ × ℝ | r ≤ q.2 ∧ q.2 ≤ Rb} := by
      ext q; simp only [hB, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [heq]; exact h1.inter h2
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro q hqA hqB
    simp only [hA, Set.mem_setOf_eq] at hqA
    simp only [hB, Set.mem_setOf_eq] at hqB
    exact hqA.1.2 hqB.1
  have hAper : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + 2 * Real.pi, q.2) ∈ A := by
    intro q
    simp only [hA, Set.mem_setOf_eq]
    rw [cov_add_two_pi q]
  have hBper : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + 2 * Real.pi, q.2) ∈ B := by
    intro q
    simp only [hB, Set.mem_setOf_eq]
    rw [cov_add_two_pi q]
  have hAsub : A ⊆ {q : ℝ × ℝ | r ≤ q.2 ∧ q.2 ≤ Rb} := by
    intro q hq; simp only [hA, Set.mem_setOf_eq] at hq; exact ⟨hq.2.1, hq.2.2⟩
  have hBsub : B ⊆ {q : ℝ × ℝ | r ≤ q.2 ∧ q.2 ≤ Rb} := by
    intro q hq; simp only [hB, Set.mem_setOf_eq] at hq; exact ⟨hq.2.1, hq.2.2⟩
  have hAbot : ∀ q ∈ A, r < q.2 := by
    intro q hq
    simp only [hA, Set.mem_setOf_eq] at hq
    by_contra hcon
    have hq2 : q.2 = r := le_antisymm (not_lt.mp hcon) hq.2.1
    have hlt : Metric.infDist (cov q) D < δ := by
      have h1 : Metric.infDist (cov q) D ≤ ‖cov q‖ := by
        have h := Metric.infDist_le_dist_of_mem (x := cov q) h0D
        rwa [dist_zero_right] at h
      rw [norm_cov, hq2, abs_of_pos hrpos] at h1
      linarith
    exact hq.1.2 (hgap (cov q) hq.1.1 hlt)
  have hBtop : ∀ q ∈ B, q.2 < Rb := by
    intro q hq
    simp only [hB, Set.mem_setOf_eq] at hq
    by_contra hcon
    have hq2 : q.2 = Rb := le_antisymm hq.2.2 (not_lt.mp hcon)
    have hRbpos : 0 < Rb := by rw [hRb]; linarith [le_max_left Cb r]
    have hnorm : ‖cov q‖ = Rb := by rw [norm_cov, hq2, abs_of_pos hRbpos]
    have hlt : ‖cov q‖ < Cb := hCb' (cov q) hq.1
    linarith
  obtain ⟨G, hGstrip, hGper, hGav⟩ :=
    periodic_path_of_split (p := 2 * Real.pi) (a := r) (b := Rb) (by positivity) hrRb
      hAclosed hBclosed hdisj hAper hBper hAsub hBsub hAbot hBtop
  refine ⟨G, ?_, ?_, hGper⟩
  · intro t; linarith [hrpos, (hGstrip t).1]
  · intro t hmem
    have hstrip := hGstrip t
    have hnotA : G t ∉ A := fun h => hGav t (Or.inl h)
    have hnotB : G t ∉ B := fun h => hGav t (Or.inr h)
    by_cases hD : cov (G t) ∈ D
    · exact hnotB (by simp only [hB, Set.mem_setOf_eq]; exact ⟨hD, hstrip.1, hstrip.2⟩)
    · exact hnotA (by
        simp only [hA, Set.mem_setOf_eq]; exact ⟨⟨hmem, hD⟩, hstrip.1, hstrip.2⟩)

/-! ## The target theorem -/

theorem bounded_component_winding_loop {K : Set ℂ} (hK : IsClosed K) (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ γ : C(Circle, ℂ), (∀ t, γ t ∈ Kᶜ) ∧
      ∃ Θ : C(ℝ, ℝ), (∀ t, Θ (t + 2 * Real.pi) = Θ t + 2 * Real.pi) ∧
        ∀ t, γ (Circle.exp t)
          = ((‖γ (Circle.exp t)‖ : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by
  obtain ⟨G, hpos, havoid, hper⟩ := periodic_path_of_bounded_component hK h0 hbdd
  obtain ⟨γ, hγ, Θ, hΘper, hΘval⟩ := exists_loop_arg_of_periodic_path G hpos hper
  refine ⟨γ, ?_, Θ, hΘper, hΘval⟩
  intro t
  obtain ⟨s, rfl⟩ := Circle.exp_surjective t
  rw [hγ s]
  exact havoid s

end

end Commons.Topology.Jordan
