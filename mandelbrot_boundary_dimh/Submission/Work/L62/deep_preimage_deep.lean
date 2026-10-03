import Mathlib
import Submission.Work.L62DP.Basic
import Submission.Work.L62DP.contraction_fp_holo

namespace Work.L62

open Filter Set Metric

/-- **Deep inverse branch, with freely chosen depths.**  Let `g` be holomorphic on an open `D`
containing the half plane `{w | w.im < Y}` and suppose `g w → 0` as `w.im → -∞` uniformly in `Re w`
(that is, along `Filter.comap Complex.im Filter.atBot`).  Then for *any* two real levels `A`, `A'`
there are half planes `{z | z.im < Lz}` (parameters) and `{v | v.im < L}` (solutions), with `L < Y`,
`L < A'` and `Lz < A` — i.e. both can be pushed arbitrarily deep — such that for every `z` in the
first one the equation `v + c + g v = z` has exactly one solution `v` in the second one, the
assignment `z ↦ u z` is holomorphic, and `u z - z + c → 0` as `z.im → -∞`.

Proof: pick a half plane `{im < T}` on which `‖g‖ < 1/4`, with `T` as deep as needed below
`min Y A'`; Cauchy's estimate (`Work.L62DP.norm_deriv_le_of_halfplane_deep`) gives `‖deriv g‖ ≤ 1/4`
on `{im < T - 1}`.  With `L = T - 2` and `Lz` below `L + c.im - 3`, the map `v ↦ z - c - g v` is a
`1/4`-contraction of the closed ball `closedBall (z - c) 1 ⊆ {im < T}` into itself; the abstract
contraction lemma `Work.L62DP.contraction_fp_holo` yields the holomorphic fixed point `u`, its
uniqueness in that ball, and, since `u z = z - c - g (u z)` with `(u z).im → -∞`, the last limit
follows from `g → 0` at the lower end. -/
theorem deep_preimage_deep {g : ℂ → ℂ} {D : Set ℂ} {c : ℂ} {Y : ℝ}
    (hD : IsOpen D) (hYsub : {w : ℂ | w.im < Y} ⊆ D) (hg : DifferentiableOn ℂ g D)
    (hlim : Filter.Tendsto g (Filter.comap Complex.im Filter.atBot) (nhds 0)) :
    ∀ A A' : ℝ, ∃ L Lz : ℝ, L < Y ∧ L < A' ∧ Lz < A ∧ ∃ u : ℂ → ℂ,
      DifferentiableOn ℂ u {z : ℂ | z.im < Lz} ∧
      (∀ z : ℂ, z.im < Lz → (u z).im < L ∧ u z + c + g (u z) = z) ∧
      (∀ z : ℂ, z.im < Lz → ∀ v : ℂ, v.im < L → v + c + g v = z → v = u z) ∧
      Filter.Tendsto (fun z => u z - z + c) (Filter.comap Complex.im Filter.atBot) (nhds 0) := by
  intro A A'
  -- (1) a deep half plane on which `‖g‖ < 1/4`, deep enough for the targets `Y` and `A'`
  obtain ⟨T₁, hT₁⟩ := (Work.L62DP.tendsto_comap_im_atBot_iff (f := g) (a := 0)).mp hlim
    (1 / 4) (by norm_num)
  set T : ℝ := min T₁ (min (Y - 1) (A' - 1)) with hTdef
  have hT_le₁ : T ≤ T₁ := min_le_left _ _
  have hT_le₂ : T ≤ min (Y - 1) (A' - 1) := min_le_right _ _
  have hT_lt_Y : T < Y := by
    have h1 : min (Y - 1) (A' - 1) ≤ Y - 1 := min_le_left _ _
    linarith
  have hT_lt_A' : T < A' := by
    have h1 : min (Y - 1) (A' - 1) ≤ A' - 1 := min_le_right _ _
    linarith
  have hgT : ∀ z : ℂ, z.im < T → ‖g z‖ < 1 / 4 := fun z hz => by
    have h := hT₁ z (lt_of_lt_of_le hz hT_le₁)
    simpa using h
  -- (2) the depth `L` of the half plane of solutions
  set L : ℝ := T - 2 with hLdef
  have hL_lt_T : L < T := by rw [hLdef]; linarith
  have hL_lt_Y : L < Y := by rw [hLdef]; linarith
  have hL_lt_A' : L < A' := by rw [hLdef]; linarith
  -- (3) holomorphy of `g` on `{im < T}` and the Cauchy derivative bound below `T - 1`
  have hsubT : {z : ℂ | z.im < T} ⊆ D := fun z hz => hYsub (lt_trans hz hT_lt_Y)
  have hholT : DifferentiableOn ℂ g {z : ℂ | z.im < T} := hg.mono hsubT
  have hderiv : ∀ u : ℂ, u.im < T - 1 → ‖deriv g u‖ ≤ 1 / 4 := fun u hu => by
    have h := Work.L62DP.norm_deriv_le_of_halfplane_deep (f := g) (Y := T) (B := 1 / 4) (r := 1)
      one_pos hholT (fun z hz => le_of_lt (hgT z hz)) hu
    simpa using h
  -- (4) the depth `Lz` of the half plane of parameters
  set Lz : ℝ := min (min (A - 1) (L + c.im - 3)) (T + c.im - 3) with hLzdef
  have hLz_lt_A : Lz < A := by
    have h1 : min (A - 1) (L + c.im - 3) ≤ A - 1 := min_le_left _ _
    have h2 : Lz ≤ min (A - 1) (L + c.im - 3) := min_le_left _ _
    linarith
  have hLz_le_L : Lz ≤ L + c.im - 3 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hLz_le_T : Lz ≤ T + c.im - 3 := min_le_right _ _
  -- (5) the balls `closedBall (z - c) 1` stay in `{im < T}`, where `g` is small
  have hball_im : ∀ z : ℂ, z.im < Lz → ∀ u : ℂ, u ∈ Metric.closedBall (z + -c) 1 → u.im < T := by
    intro z hz u hu
    have h1 : u.im ≤ (z + -c).im + 1 := Work.L62DP.im_le_of_mem_closedBall hu
    have h1' : u.im ≤ z.im - c.im + 1 := by
      have h2 := h1
      simp only [Complex.add_im, Complex.neg_im] at h2
      linarith
    have h3 : z.im < L + c.im - 3 := lt_of_lt_of_le hz hLz_le_L
    linarith
  have hball : ∀ w ∈ {z : ℂ | z.im < Lz},
      Metric.closedBall (w + (-c)) 1 ⊆ {z : ℂ | z.im < T} :=
    fun w hw u hu => hball_im w hw u hu
  have hsmall : ∀ w ∈ {z : ℂ | z.im < Lz},
      ∀ u ∈ Metric.closedBall (w + (-c)) 1, ‖g u‖ ≤ (1 - 1 / 4) * 1 := by
    intro w hw u hu
    have h1 : u.im < T := hball_im w hw u hu
    have h2 : ‖g u‖ ≤ 1 / 4 := le_of_lt (hgT u h1)
    nlinarith
  have hlip : ∀ w ∈ {z : ℂ | z.im < Lz},
      ∀ u ∈ Metric.closedBall (w + (-c)) 1, ‖deriv g u‖ ≤ 1 / 4 := by
    intro w hw u hu
    have h1 : u.im ≤ (w + -c).im + 1 := Work.L62DP.im_le_of_mem_closedBall hu
    have h1' : u.im ≤ w.im - c.im + 1 := by
      have h2 := h1
      simp only [Complex.add_im, Complex.neg_im] at h2
      linarith
    have h3 : w.im < L + c.im - 3 := lt_of_lt_of_le hw hLz_le_L
    refine hderiv u ?_
    linarith
  -- (6) the abstract contraction lemma
  obtain ⟨u, hu_diff, hu_fix, hu_uniq⟩ :=
    Work.L62DP.contraction_fp_holo (s := {z : ℂ | z.im < Lz}) (Omega := {z : ℂ | z.im < T})
      (Psi := g) (beta := -c) (r := 1) (lam := 1 / 4)
      (isOpen_lt Complex.continuous_im continuous_const)
      (isOpen_lt Complex.continuous_im continuous_const)
      hholT one_pos (by norm_num) (by norm_num) hball hsmall hlip
  refine ⟨L, Lz, hL_lt_Y, hL_lt_A', hLz_lt_A, u, hu_diff, ?_, ?_, ?_⟩
  · -- the fixed point lies in `{im < L}` and solves `v + c + g v = z`
    intro z hz
    obtain ⟨hzball, hzfix⟩ := hu_fix z hz
    have h1 : (u z).im ≤ (z + -c).im + 1 := Work.L62DP.im_le_of_mem_closedBall hzball
    have h1' : (u z).im ≤ z.im - c.im + 1 := by
      have h2 := h1
      simp only [Complex.add_im, Complex.neg_im] at h2
      linarith
    have h2 : z.im < L + c.im - 3 := lt_of_lt_of_le hz hLz_le_L
    refine ⟨by linarith, ?_⟩
    nth_rewrite 1 [hzfix]
    ring
  · -- uniqueness in `{im < L}`
    intro z hz v hv hveq
    have hvT : v.im < T := by rw [hLdef] at hv; linarith
    have hgv : ‖g v‖ < 1 / 4 := hgT v hvT
    have hv_eq : v = z + (-c) - g v := by linear_combination hveq
    have hv_mem : v ∈ Metric.closedBall (z + (-c)) 1 := by
      refine Work.L62DP.mem_closedBall_of_le ?_
      have hsub : (z + (-c) - g v) - (z + (-c)) = -g v := by ring
      rw [hv_eq, hsub, norm_neg]
      linarith
    exact hu_uniq z hz v hv_mem hv_eq
  · -- asymptotics: `u z - z + c = -g (u z) → 0` at the lower end
    have hge : Filter.Tendsto (fun z : ℂ => g (u z))
        (Filter.comap Complex.im Filter.atBot) (nhds 0) := by
      refine (Work.L62DP.tendsto_comap_im_atBot_iff (f := fun z : ℂ => g (u z)) (a := 0)).mpr ?_
      intro ε hε
      obtain ⟨Tε, hTε⟩ :=
        (Work.L62DP.tendsto_comap_im_atBot_iff (f := g) (a := 0)).mp hlim ε hε
      refine ⟨min Lz (Tε + c.im - 1), fun z hz => ?_⟩
      have hzLz : z.im < Lz := lt_of_lt_of_le hz (min_le_left _ _)
      have hzT : z.im < Tε + c.im - 1 := lt_of_lt_of_le hz (min_le_right _ _)
      obtain ⟨hzball, -⟩ := hu_fix z hzLz
      have h1 : (u z).im ≤ (z + -c).im + 1 := Work.L62DP.im_le_of_mem_closedBall hzball
      have h1' : (u z).im ≤ z.im - c.im + 1 := by
        have h2 := h1
        simp only [Complex.add_im, Complex.neg_im] at h2
        linarith
      have h2 : (u z).im < Tε := by linarith
      have h3 := hTε (u z) h2
      simpa using h3
    have hneg : Filter.Tendsto (fun z : ℂ => -(g (u z)))
        (Filter.comap Complex.im Filter.atBot) (nhds 0) := by
      simpa using hge.neg
    refine Filter.Tendsto.congr' ?_ hneg
    filter_upwards [Work.L62DP.mem_comap_im_atBot_iff.mpr ⟨Lz, fun z hz => hz⟩] with z hz
    obtain ⟨-, hzfix⟩ := hu_fix z hz
    have hkey : u z - z + c = -(g (u z)) := by
      nth_rewrite 1 [hzfix]
      ring
    exact hkey.symm

end Work.L62
