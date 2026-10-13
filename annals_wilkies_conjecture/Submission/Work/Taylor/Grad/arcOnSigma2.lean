import Mathlib
import Submission.Work.WilE3.Taylor.Grad.badSeqOnPolarSet
import Submission.Work.WilE3.Taylor.Grad.arcOnSigma

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology

namespace Work.Taylor.Grad

/-!
  annals_wilkies_conjecture, AREA Taylor / Grad: *the arc on the `det3`-locus*, companion of
  `Work.WilE3.Taylor.Grad.arcOnSigma` and `Work.WilE3.Taylor.Grad.arcOnPolarSet`.

  The hypothesis is the *second* alternative of `Work.WilE3.Taylor.Grad.badSeqOnPolarSet`: points
  `x` arbitrarily close to `y` with `Φ x > 0`, `(‖∇Φ x‖²)^q < (Φ x)^{2p}` and with the three
  vectors `∇‖∇Φ‖²`, `∇Φ` and `x - y` linearly dependent (all `3 × 3` minors `det3` vanish).  The
  conclusion is a real analytic arc through `y` staying in that locus for all small `t > 0`.

  The set
  `Σ = {Φ > 0} ∩ {(Φ)^{2p} − (‖∇Φ‖²)^q > 0} ∩ {det3 (∇‖∇Φ‖²) (∇Φ) (· − y) = 0}`
  is basic semianalytic with data analytic at `y` (`analyticAt_det3Fun`), and `y` lies in its
  closure by `hseq`.  `Work.WilE3.Loj.curveSel_full` then produces an analytic arc `γ` through `y`
  lying in `Σ` for all small `s > 0`.  Since `CurveSel` has no nonconstancy clause, the arc might
  be the constant arc at `y` if `y ∈ Σ`; the hypothesis `Φ y = 0` of `arcOnSigma` rules this out
  there, but here we again use the trick of `arcOnPolarSet`: intersecting `Σ` with one extra
  inequality `0 < s · (x i − y i)` (chosen so that infinitely many of the points `x n` satisfy it)
  keeps `y` in the closure and forces the selected arc to be nonconstant, hence `γ t ≠ y` for all
  small `t > 0`.  Note that `p < q` is not used; only the existence of the sequence matters.
-/

/-! ## §1. The `det3` entries and their sum of squares -/

/-- The `(i,j,l)` entry of the determinant `det3 (∇‖∇Φ‖²) (∇Φ) (x - y)`: the target's tangency
condition is exactly `det3Fun Φ y i j l x = 0` for all `i j l`. -/
noncomputable def det3Fun {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (y : Fin k → ℝ)
    (i j l : Fin k) : (Fin k → ℝ) → ℝ :=
  fun x => Work.WilE3.Taylor.Grad.det3
    (fun m => Work.WilE3.Taylor.grad (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) x m)
    (fun m => Work.WilE3.Taylor.grad Φ x m) (x - y) i j l

/-- Coordinate functions are analytic. -/
lemma analyticAt_subCoord {k : ℕ} (y : Fin k → ℝ) (m : Fin k) :
    AnalyticAt ℝ (fun x : Fin k → ℝ => x m - y m) y := by
  have hcoord : AnalyticAt ℝ (fun x : Fin k → ℝ => x m) y := by
    have h := ContinuousLinearMap.analyticAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) m) y
    refine h.congr ?_
    filter_upwards with x
    exact ContinuousLinearMap.proj_apply m x
  exact hcoord.sub analyticAt_const

/-- `det3` of three pointwise-analytic rows is pointwise analytic. -/
lemma analyticAt_det3 {k : ℕ} {u w t : (Fin k → ℝ) → Fin k → ℝ} {y : Fin k → ℝ}
    (hu : ∀ i, AnalyticAt ℝ (fun x => u x i) y)
    (hw : ∀ i, AnalyticAt ℝ (fun x => w x i) y)
    (ht : ∀ i, AnalyticAt ℝ (fun x => t x i) y) (i j l : Fin k) :
    AnalyticAt ℝ (fun x => Work.WilE3.Taylor.Grad.det3 (u x) (w x) (t x) i j l) y := by
  simp only [Work.WilE3.Taylor.Grad.det3]
  exact (((hu i).mul (((hw j).mul (ht l)).sub ((hw l).mul (ht j)))).sub
    (((hu j).mul (((hw i).mul (ht l)).sub ((hw l).mul (ht i)))))).add
    ((hu l).mul (((hw i).mul (ht j)).sub ((hw j).mul (ht i))))

/-- Each `det3` entry is analytic at `y` when `Φ` is. -/
lemma analyticAt_det3Fun {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ}
    (h : AnalyticAt ℝ Φ y) (i j l : Fin k) : AnalyticAt ℝ (det3Fun Φ y i j l) y := by
  have hS : AnalyticAt ℝ (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) y :=
    Work.WilE3.Taylor.Grad.analyticAt_gradSumSq h
  refine analyticAt_det3
    (u := fun x m => Work.WilE3.Taylor.grad
      (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) x m)
    (w := fun x m => Work.WilE3.Taylor.grad Φ x m)
    (t := fun x => x - y) ?_ ?_ ?_ i j l
  · intro m; exact Work.WilE3.Taylor.Grad.analyticAt_grad hS m
  · intro m; exact Work.WilE3.Taylor.Grad.analyticAt_grad h m
  · intro m; exact analyticAt_subCoord y m

/-- `sigma2Fun Φ y x = ∑_{i,j,l} (det3 entry)²`: the sum of the squares of all the entries, so that
it vanishes exactly at the points where `∇‖∇Φ‖²`, `∇Φ` and `x - y` are linearly dependent. -/
noncomputable def sigma2Fun {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (y : Fin k → ℝ) :
    (Fin k → ℝ) → ℝ :=
  fun x => ∑ p : Fin k × Fin k × Fin k, (det3Fun Φ y p.1 p.2.1 p.2.2 x) ^ 2

/-- `sigma2Fun` is analytic at `y` when `Φ` is. -/
lemma analyticAt_sigma2Fun {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ}
    (h : AnalyticAt ℝ Φ y) : AnalyticAt ℝ (sigma2Fun Φ y) y := by
  have hsum := Finset.analyticAt_sum (Finset.univ : Finset (Fin k × Fin k × Fin k))
    (fun p _ => (analyticAt_det3Fun h p.1 p.2.1 p.2.2).pow 2)
  have hfun : (∑ p : Fin k × Fin k × Fin k,
      (fun x => det3Fun Φ y p.1 p.2.1 p.2.2 x) ^ 2 : (Fin k → ℝ) → ℝ)
      = fun x => ∑ p : Fin k × Fin k × Fin k, (det3Fun Φ y p.1 p.2.1 p.2.2 x) ^ 2 := by
    funext x; simp [Finset.sum_apply, Pi.pow_apply]
  rw [hfun] at hsum
  exact hsum

/-- A vanishing sum of squares vanishes termwise: the linear dependence of the three vectors. -/
lemma det3Fun_eq_zero_of_sigma2Fun_eq_zero {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y z : Fin k → ℝ}
    (h : sigma2Fun Φ y z = 0) (i j l : Fin k) : det3Fun Φ y i j l z = 0 := by
  have h' : ∑ p : Fin k × Fin k × Fin k, (det3Fun Φ y p.1 p.2.1 p.2.2 z) ^ 2 = 0 := h
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun p : Fin k × Fin k × Fin k => (det3Fun Φ y p.1 p.2.1 p.2.2 z) ^ 2)
      (fun p _ => sq_nonneg _)).mp h'
  exact sq_eq_zero_iff.mp (hterm (i, j, l) (Finset.mem_univ _))

/-! ## §2. The two strict inequalities, plus the nonconstancy inequality -/

/-- The strict inequalities of the target as a `Fin 3`-family, together with the auxiliary
inequality `0 < s · (x i − y i)` used to force the selected arc to be nonconstant: coordinate `0`
is `Φ > 0`, coordinate `1` is `(Φ)^{2p} - (∑ l, (∇Φ l)²)^q > 0`, coordinate `2` is
`s · (x i − y i) > 0`. -/
noncomputable def pos2Fun {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (p q : ℕ) (y : Fin k → ℝ)
    (i : Fin k) (s : ℝ) : Fin 3 → (Fin k → ℝ) → ℝ :=
  ![fun x => Φ x,
    fun x => (Φ x) ^ (2 * p) - (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q,
    fun x => s * (x i - y i)]

lemma pos2Fun_zero {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (p q : ℕ) (y : Fin k → ℝ)
    (i : Fin k) (s : ℝ) :
    pos2Fun Φ p q y i s 0 = (fun x : Fin k → ℝ => Φ x) := by
  simp [pos2Fun]

lemma pos2Fun_one {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (p q : ℕ) (y : Fin k → ℝ)
    (i : Fin k) (s : ℝ) :
    pos2Fun Φ p q y i s 1
      = (fun x : Fin k → ℝ => (Φ x) ^ (2 * p)
          - (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q) := by
  simp [pos2Fun]

lemma pos2Fun_two {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (p q : ℕ) (y : Fin k → ℝ)
    (i : Fin k) (s : ℝ) :
    pos2Fun Φ p q y i s 2 = (fun x : Fin k → ℝ => s * (x i - y i)) := by
  simp [pos2Fun]

/-- Each member of the `Fin 3`-family is analytic at `y`. -/
lemma analyticAt_pos2Fun {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {p q : ℕ}
    (hΦ : AnalyticAt ℝ Φ y) (i : Fin k) (s : ℝ) (j : Fin 3) :
    AnalyticAt ℝ (pos2Fun Φ p q y i s j) y := by
  have hS : AnalyticAt ℝ (fun x => ∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) y :=
    Work.WilE3.Taylor.Grad.analyticAt_gradSumSq hΦ
  fin_cases j
  · change AnalyticAt ℝ (pos2Fun Φ p q y i s 0) y
    rw [pos2Fun_zero]; exact hΦ
  · change AnalyticAt ℝ (pos2Fun Φ p q y i s 1) y
    rw [pos2Fun_one]; exact (hΦ.pow (2 * p)).sub (hS.pow q)
  · change AnalyticAt ℝ (pos2Fun Φ p q y i s 2) y
    rw [pos2Fun_two]
    exact analyticAt_const.mul (analyticAt_subCoord y i)

/-! ## §3. The arc -/

theorem arcOnSigma2 {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {p q : ℕ}
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) (hpq : p < q)
    (hseq : ∀ n : ℕ, ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < 1 / (n + 1) ∧ 0 < Φ x ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p) ∧
      (∀ i j l : Fin k, Work.WilE3.Taylor.Grad.det3
        (fun m => Work.WilE3.Taylor.grad (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) x m)
        (fun m => Work.WilE3.Taylor.grad Φ x m) (x - y) i j l = 0)) :
    ∃ γ : ℝ → Fin k → ℝ, AnalyticAt ℝ γ 0 ∧ γ 0 = y ∧
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ t ≠ y ∧ 0 < Φ (γ t) ∧
        (∑ l, (Work.WilE3.Taylor.grad Φ (γ t) l) ^ 2) ^ q < (Φ (γ t)) ^ (2 * p) ∧
        (∀ i j l : Fin k, Work.WilE3.Taylor.Grad.det3
          (fun m => Work.WilE3.Taylor.grad (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) (γ t) m)
          (fun m => Work.WilE3.Taylor.grad Φ (γ t) m) (γ t - y) i j l = 0) := by
  have _hpq := hpq
  -- restate the sequence hypothesis in the vocabulary of this file
  have hseq' : ∀ n : ℕ, ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < 1 / (n + 1) ∧ 0 < Φ x ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p) ∧
      (∀ i j l : Fin k, det3Fun Φ y i j l x = 0) := by
    intro n
    obtain ⟨x, h1, h2, h3, h4, h5⟩ := hseq n
    exact ⟨x, h1, h2, h3, h4, fun i j l => by simpa only [det3Fun] using h5 i j l⟩
  choose x hxne hxd hxpos hxlt hxtan using hseq'
  -- the good points tend to `y`
  have hx_tendsto : Tendsto x atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hxd n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- Some coordinate separates `x n` from `y` along an infinite subsequence.
  have hinf : ∃ i : Fin k, Set.Infinite {n : ℕ | x n i ≠ y i} := by
    by_contra hcon
    simp only [not_exists, Set.not_infinite] at hcon
    have hsub : (Set.univ : Set ℕ) ⊆ ⋃ i : Fin k, {n : ℕ | x n i ≠ y i} := by
      intro n _
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra h
      push_neg at h
      exact hxne n (funext h)
    have hfin : (Set.univ : Set ℕ).Finite :=
      Set.Finite.subset (Set.finite_iUnion (fun i : Fin k => hcon i)) hsub
    exact Set.infinite_univ hfin
  obtain ⟨i, hi⟩ := hinf
  -- ... and there is a sign `s ∈ {±1}` keeping the sign condition along it.
  have hdir : Set.Infinite {n : ℕ | 0 < x n i - y i} ∨
      Set.Infinite {n : ℕ | 0 < y i - x n i} := by
    by_contra h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    refine hi (Set.Finite.subset (h1.union h2) ?_)
    intro n hn
    simp only [Set.mem_union, Set.mem_setOf_eq] at hn ⊢
    rcases lt_trichotomy (x n i) (y i) with hlt | heq | hgt
    · exact Or.inr (by linarith)
    · exact absurd heq hn
    · exact Or.inl (by linarith)
  have hex : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      Set.Infinite {n : ℕ | 0 < s * (x n i - y i)} := by
    rcases hdir with hdir | hdir
    · exact ⟨1, Or.inl rfl, by simpa using hdir⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have hset : {n : ℕ | 0 < -1 * (x n i - y i)} = {n : ℕ | 0 < y i - x n i} := by
        ext n
        simp only [Set.mem_setOf_eq]
        constructor <;> intro h <;> linarith
      rw [hset]; exact hdir
  obtain ⟨s, -, hA⟩ := hex
  let Sset : Set (Fin k → ℝ) :=
    WilkiesDesign.CG.C4a.BasicSA (sigma2Fun Φ y) (pos2Fun Φ p q y i s)
  have hmemS : ∀ n ∈ ({n : ℕ | 0 < s * (x n i - y i)} : Set ℕ), x n ∈ Sset := by
    intro n hn
    refine ⟨?_, ?_⟩
    · have hsum : ∑ p : Fin k × Fin k × Fin k, (det3Fun Φ y p.1 p.2.1 p.2.2 (x n)) ^ 2 = 0 := by
        refine Finset.sum_eq_zero (fun p _ => ?_)
        rw [hxtan n p.1 p.2.1 p.2.2]
        simp
      simpa only [Sset, sigma2Fun] using hsum
    · intro j
      fin_cases j
      · change 0 < pos2Fun Φ p q y i s 0 (x n)
        rw [pos2Fun_zero]; exact hxpos n
      · change 0 < pos2Fun Φ p q y i s 1 (x n)
        rw [pos2Fun_one]; exact sub_pos.mpr (hxlt n)
      · change 0 < pos2Fun Φ p q y i s 2 (x n)
        rw [pos2Fun_two]; exact hn
  have hycl : y ∈ closure Sset := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hx_tendsto) ε hε
    obtain ⟨n, hnA, hnN⟩ := hA.exists_gt N
    exact ⟨x n, hmemS n hnA, by simpa [dist_comm] using hN n (le_of_lt hnN)⟩
  -- analytic curve selection
  obtain ⟨γ, hγan, hγ0, ε, hεpos, hγmem⟩ :=
    Work.WilE3.Loj.curveSel_full k 3 (sigma2Fun Φ y) (pos2Fun Φ p q y i s) y
      (analyticAt_sigma2Fun (hΦ y))
      (fun j => analyticAt_pos2Fun (hΦ y) i s j) hycl
  refine ⟨γ, hγan, hγ0, ?_⟩
  have hnb : Set.Ioo (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hεpos))
  filter_upwards [hnb] with t ht
  have hsig : sigma2Fun Φ y (γ t) = 0 := (hγmem t ht).1
  have hpos : 0 < Φ (γ t) := by
    have h := (hγmem t ht).2 0
    rw [pos2Fun_zero] at h
    exact h
  have hineq : (∑ l, (Work.WilE3.Taylor.grad Φ (γ t) l) ^ 2) ^ q < (Φ (γ t)) ^ (2 * p) := by
    have h := (hγmem t ht).2 1
    rw [pos2Fun_one] at h
    linarith
  have hne : γ t ≠ y := by
    intro heq
    have h := (hγmem t ht).2 2
    rw [pos2Fun_two] at h
    rw [heq] at h
    simp at h
  exact ⟨hne, hpos, hineq, fun a b c => by
    have h := det3Fun_eq_zero_of_sigma2Fun_eq_zero hsig a b c
    simpa only [det3Fun] using h⟩

end Work.Taylor.Grad
