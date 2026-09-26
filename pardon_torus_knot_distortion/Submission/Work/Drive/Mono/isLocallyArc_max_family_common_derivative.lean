import Mathlib
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_pair
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Drive.Mono.two_arcs_glue
import Submission.Work.Drive.Mono.graph_snd_slope
import Submission.Work.Drive.Mono.family_max_graph_slope

/-!
# The zero set of `max (maxᵢ ψᵢ) G` near a common regular zero with a transverse `G`

Let `ψᵢ` (`i` in a finite nonempty index type) be `C¹` functions vanishing at `p` with a common
nonzero derivative `D = fderiv ℝ (ψᵢ) p`, and let `G` be `C¹` with `G p = 0` and
`fderiv ℝ G p` *not* a multiple of `D` (so the zero set of `G` meets the common level set of the
`ψᵢ` transversally at `p`).  Then near `p` the zero set of `q ↦ max (maxᵢ ψᵢ q) (G q)` is a
topological arc — in fact a "V" made of one branch of the common zero set and one branch of
`{G = 0}`; a neighbourhood `V` of `p` is produced on which this holds.

The proof straightens the two functionals into the coordinate functions (`L = (D, fderiv G p)` is
invertible because the two functionals are linearly independent), reduces to functions with
`fderiv = fst` resp. `snd` at the origin, and glues two arcs (`two_arcs_glue`).
-/

namespace Work.Drive.Mono

open Set

private lemma nonpos_of_le_abs_div_four {a : ℝ} (h : a ≤ |a| / 4) : a ≤ 0 := by
  by_contra hcon
  have ha : 0 < a := not_le.mp hcon
  rw [abs_of_pos ha] at h
  linarith

private lemma nonpos_of_sub_abs {y m : ℝ} (hm : m ≤ 0) (h : |m - y| ≤ 3 * |y| / 8) : y ≤ 0 := by
  by_contra hcon
  have hy : 0 < y := not_le.mp hcon
  have h6 : y - m ≤ |m - y| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have h5 : |y| = y := abs_of_pos hy
  rw [h5] at h
  linarith

private lemma norm_prod_le_abs_add (a b : ℝ) : ‖(a, b)‖ ≤ |a| + |b| := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_right (abs_nonneg b)) (le_add_of_nonneg_left (abs_nonneg a))

private lemma clm_apply_eq (D : (ℝ × ℝ) →L[ℝ] ℝ) (z : ℝ × ℝ) :
    D z = D (1, 0) * z.1 + D (0, 1) * z.2 := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
  nth_rewrite 1 [hz]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The model computation.**  Suppose that, in a neighbourhood of the origin, the set
`{F ≤ 0}` is the region `{x ≤ φ y}` to the right of the graph of a continuous `φ` with
`|φ y| ≤ |y|/2`, that `{g ≤ 0}` is the region `{y ≤ ψ x}` below the graph of a continuous `ψ`
with `|ψ x| ≤ |x|/2`, and that `g` is `y + o(‖(x,y)‖)`.  Then the zero set of `max F g` is
locally an arc.

Concretely the two graphs `x = φ y` and `y = ψ x` cross transversally at the origin, and the zero
set is the union of the branch `y ≤ 0` of the first and the branch `x ≤ 0` of the second; these
are two arcs meeting exactly at the origin (`two_arcs_glue`). -/
theorem isLocallyArc_of_family_data {F g : ℝ × ℝ → ℝ} {φ ψ : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ ρ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hρ : 0 < ρ)
    (hφ : ContinuousOn φ (Set.Ioo (-A₂) A₂)) (hφ0 : φ 0 = 0)
    (hφs : ∀ y : ℝ, |y| ≤ A₂ → |φ y| ≤ |y| / 2)
    (hψ : ContinuousOn ψ (Set.Ioo (-B₁) B₁)) (hψ0 : ψ 0 = 0)
    (hψs : ∀ x : ℝ, |x| ≤ B₁ → |ψ x| ≤ |x| / 2)
    (hFs : ∀ x y : ℝ, |x| ≤ A₁ → |y| ≤ A₂ →
      (F (x, y) ≤ 0 ↔ x ≤ φ y) ∧ (F (x, y) = 0 ↔ x = φ y))
    (hgs : ∀ x y : ℝ, |x| ≤ B₁ → |y| ≤ B₂ →
      (g (x, y) ≤ 0 ↔ y ≤ ψ x) ∧ (g (x, y) = 0 ↔ y = ψ x))
    (hglin : ∀ z : ℝ × ℝ, ‖z‖ ≤ ρ → |g z - z.2| ≤ ‖z‖ / 4) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (0 : ℝ × ℝ) ∈ V ∧
      Work.Smooth.SphereJordan.IsLocallyArc
        ↥(V ∩ {q : ℝ × ℝ | max (F q) (g q) = 0}) := by
  set R₁ : ℝ := min (min (min A₁ (B₁ / 2)) (min A₂ (2 * B₂))) (4 * ρ / 3) with hR₁def
  set R₂ : ℝ := min (min (A₂ / 2) B₂) (min (2 * ρ / 3) R₁) with hR₂def
  have hR₁_le_A₁ : R₁ ≤ A₁ := by
    rw [hR₁def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hR₁_le_halfB₁ : R₁ ≤ B₁ / 2 := by
    rw [hR₁def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hR₁_le_A₂ : R₁ ≤ A₂ := by
    rw [hR₁def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hR₁_le_2B₂ : R₁ ≤ 2 * B₂ := by
    rw [hR₁def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hR₁_le_4ρ : R₁ ≤ 4 * ρ / 3 := min_le_right _ _
  have hR₁pos : 0 < R₁ := by
    rw [hR₁def]
    exact lt_min (lt_min (lt_min hA₁ (by linarith)) (lt_min hA₂ (by linarith))) (by linarith)
  have hR₁_lt_B₁ : R₁ < B₁ := lt_of_le_of_lt hR₁_le_halfB₁ (by linarith)
  have hR₁_le_B₁ : R₁ ≤ B₁ := hR₁_lt_B₁.le
  have hR₂_le_halfA₂ : R₂ ≤ A₂ / 2 := by
    rw [hR₂def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₂_le_B₂ : R₂ ≤ B₂ := by
    rw [hR₂def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₂_le_2ρ : R₂ ≤ 2 * ρ / 3 := by
    rw [hR₂def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hR₂_le_R₁ : R₂ ≤ R₁ := by
    rw [hR₂def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hR₂pos : 0 < R₂ := by
    rw [hR₂def]
    exact lt_min (lt_min (by linarith) hB₂) (lt_min (by linarith) hR₁pos)
  have hR₂_lt_A₂ : R₂ < A₂ := lt_of_le_of_lt hR₂_le_halfA₂ (by linarith)
  have hR₂_le_A₂ : R₂ ≤ A₂ := hR₂_lt_A₂.le
  have hhalf : R₁ / 2 ≤ R₂ := by
    rw [hR₂def]
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · linarith [hR₁_le_A₂]
    · linarith [hR₁_le_2B₂]
    · linarith [hR₁_le_4ρ, hρ]
    · linarith [hR₁pos]
  have hhalf₂ : R₂ / 2 ≤ R₁ := by linarith [hR₂_le_R₁, hR₁pos]
  have hglinφ : ∀ y : ℝ, |y| ≤ R₂ → |g (φ y, y) - y| ≤ 3 * |y| / 8 := by
    intro y hy
    have h1 : |φ y| ≤ |y| / 2 := hφs y (le_trans hy hR₂_le_A₂)
    have h3 : ‖(φ y, y)‖ ≤ |φ y| + |y| := norm_prod_le_abs_add _ _
    have h4 : ‖(φ y, y)‖ ≤ ρ := by
      have h5 : (3 : ℝ) * |y| / 2 ≤ ρ := by linarith [hy, hR₂_le_2ρ, hρ]
      linarith
    have h5 := hglin (φ y, y) h4
    have h6 : ‖(φ y, y)‖ ≤ 3 * |y| / 2 := by linarith
    linarith
  set γ₁ : ℝ → ℝ × ℝ := fun y => (φ y, y) with hγ₁def
  set γ₂ : ℝ → ℝ × ℝ := fun x => (x, ψ x) with hγ₂def
  set V : Set (ℝ × ℝ) := {q : ℝ × ℝ | |q.1| < R₁ ∧ |q.2| < R₂} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact (isOpen_lt (continuous_fst.abs) continuous_const).inter
      (isOpen_lt (continuous_snd.abs) continuous_const)
  have h0V : (0 : ℝ × ℝ) ∈ V := by
    rw [hVdef]
    refine ⟨by simpa using hR₁pos, by simpa using hR₂pos⟩
  have hmain : V ∩ {q : ℝ × ℝ | max (F q) (g q) = 0}
      = γ₁ '' Set.Ioc (-R₂) 0 ∪ γ₂ '' Set.Ioc (-R₁) 0 := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqV, hqZ⟩ := hq
      have hq1 : |q.1| < R₁ := hqV.1
      have hq2 : |q.2| < R₂ := hqV.2
      have hq1A₁ : |q.1| ≤ A₁ := le_trans hq1.le hR₁_le_A₁
      have hq2A₂ : |q.2| ≤ A₂ := le_of_lt (lt_trans hq2 hR₂_lt_A₂)
      have hq1B₁ : |q.1| ≤ B₁ := le_trans hq1.le hR₁_le_B₁
      have hq2B₂ : |q.2| ≤ B₂ := le_trans hq2.le hR₂_le_B₂
      obtain ⟨hF_le, hF_eq⟩ := hFs q.1 q.2 hq1A₁ hq2A₂
      obtain ⟨hg_le, hg_eq⟩ := hgs q.1 q.2 hq1B₁ hq2B₂
      obtain ⟨hF_le0, hg_le0, hor⟩ :=
        (Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff).mp hqZ
      have hq1_le : q.1 ≤ φ q.2 := hF_le.mp hF_le0
      have hq2_le : q.2 ≤ ψ q.1 := hg_le.mp hg_le0
      rcases hor with hF0 | hg0
      · have hq1_eq : q.1 = φ q.2 := hF_eq.mp hF0
        have hφq2b : |φ q.2| ≤ |q.2| / 2 := hφs q.2 (le_of_lt (lt_trans hq2 hR₂_lt_A₂))
        have hφq2B₁ : |φ q.2| ≤ B₁ := by
          have h : |φ q.2| < R₁ := by
            have h' : |q.2| / 2 < R₂ / 2 := by linarith
            linarith
          exact le_trans h.le hR₁_le_B₁
        have hgz : g (φ q.2, q.2) ≤ 0 := by
          refine ((hgs (φ q.2) q.2 hφq2B₁ hq2B₂).1).mpr ?_
          rw [← hq1_eq]
          exact hq2_le
        have hq2_nonpos : q.2 ≤ 0 := nonpos_of_sub_abs hgz (hglinφ q.2 hq2.le)
        refine Or.inl ⟨q.2, ?_, ?_⟩
        · rw [Set.mem_Ioc]
          exact ⟨(abs_lt.mp hq2).1, hq2_nonpos⟩
        · show (φ q.2, q.2) = q
          exact Prod.ext hq1_eq.symm rfl
      · have hq2_eq : q.2 = ψ q.1 := hg_eq.mp hg0
        have hq1_le' : q.1 ≤ φ (ψ q.1) := by
          rw [← hq2_eq]
          exact hq1_le
        have hφψb : |φ (ψ q.1)| ≤ |q.1| / 4 := by
          have h2 : |ψ q.1| ≤ A₂ := by
            have h1 : |ψ q.1| ≤ |q.1| / 2 := hψs q.1 hq1B₁
            linarith [hq1, hR₁_le_A₂]
          have h3 := hφs (ψ q.1) h2
          linarith [hψs q.1 hq1B₁]
        have hq1_nonpos : q.1 ≤ 0 := by
          refine nonpos_of_le_abs_div_four ?_
          exact le_trans hq1_le' (le_trans (le_abs_self _) hφψb)
        refine Or.inr ⟨q.1, ?_, ?_⟩
        · rw [Set.mem_Ioc]
          exact ⟨(abs_lt.mp hq1).1, hq1_nonpos⟩
        · show (q.1, ψ q.1) = q
          exact Prod.ext rfl hq2_eq.symm
    · rintro (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
      · rw [Set.mem_Ioc] at hy
        obtain ⟨hy_gt, hy_le⟩ := hy
        have hyabs : |y| ≤ R₂ := abs_le.mpr ⟨hy_gt.le, le_trans hy_le hR₂pos.le⟩
        have hyabs_lt : |y| < R₂ := by
          rw [abs_lt]
          exact ⟨hy_gt, lt_of_le_of_lt hy_le hR₂pos⟩
        have hφb : |φ y| ≤ |y| / 2 := hφs y (le_trans hyabs hR₂_le_A₂)
        refine ⟨⟨?_, hyabs_lt⟩, ?_⟩
        · have h' : |y| / 2 < R₂ / 2 := by linarith
          linarith [hφb, h', hhalf₂]
        · have hF0 : F (φ y, y) = 0 :=
            ((hFs (φ y) y (by linarith [hφb, hyabs, hhalf₂, hR₁_le_A₁])
              (le_trans hyabs hR₂_le_A₂)).2).mpr rfl
          have hgl := hglinφ y hyabs
          have hyabs_eq : |y| = -y := abs_of_nonpos hy_le
          have hgz : g (φ y, y) ≤ 0 := by
            have h1 : g (φ y, y) - y ≤ |g (φ y, y) - y| := le_abs_self _
            linarith
          show max (F (φ y, y)) (g (φ y, y)) = 0
          rw [hF0]
          exact max_eq_left hgz
      · rw [Set.mem_Ioc] at hx
        obtain ⟨hx_gt, hx_le⟩ := hx
        have hxabs : |x| ≤ R₁ := abs_le.mpr ⟨hx_gt.le, le_trans hx_le hR₁pos.le⟩
        have hxabs_lt : |x| < R₁ := by
          rw [abs_lt]
          exact ⟨hx_gt, lt_of_le_of_lt hx_le hR₁pos⟩
        have hψb : |ψ x| ≤ |x| / 2 := hψs x (le_trans hxabs hR₁_le_B₁)
        refine ⟨⟨hxabs_lt, ?_⟩, ?_⟩
        · have h' : |x| / 2 < R₁ / 2 := by linarith
          linarith [hψb, h', hhalf]
        · have hψA₂ : |ψ x| ≤ A₂ := by linarith [hψb, hxabs, hR₁_le_A₂]
          have hψB₂ : |ψ x| ≤ B₂ := by linarith [hψb, hxabs, hhalf, hR₂_le_B₂]
          have hg0 : g (x, ψ x) = 0 :=
            ((hgs x (ψ x) (le_trans hxabs hR₁_le_B₁) hψB₂).2).mpr rfl
          have hφψb : |φ (ψ x)| ≤ |x| / 4 := by
            have h3 := hφs (ψ x) hψA₂
            linarith [hψb]
          have hxabs_eq : |x| = -x := abs_of_nonpos hx_le
          have hle : x ≤ φ (ψ x) := by
            have h1 := neg_abs_le (φ (ψ x))
            linarith
          have hF : F (x, ψ x) ≤ 0 :=
            ((hFs x (ψ x) (le_trans hxabs hR₁_le_A₁) hψA₂).1).mpr hle
          show max (F (x, ψ x)) (g (x, ψ x)) = 0
          rw [hg0]
          exact max_eq_right hF
  have hcont₁ : ContinuousOn γ₁ (Set.Icc (-R₂) 0) := by
    have hp : ContinuousOn (fun y : ℝ => (φ y, y)) (Set.Ioo (-A₂) A₂) :=
      hφ.prodMk continuousOn_id
    refine hp.mono ?_
    intro y hy
    rw [Set.mem_Icc] at hy
    rw [Set.mem_Ioo]
    have hyabs : |y| ≤ R₂ := abs_le.mpr ⟨hy.1, le_trans hy.2 hR₂pos.le⟩
    exact ⟨by linarith [hR₂_lt_A₂, (abs_le.mp hyabs).1], by linarith [hR₂_lt_A₂, hA₂, hy.2]⟩
  have hcont₂ : ContinuousOn γ₂ (Set.Icc (-R₁) 0) := by
    have hp : ContinuousOn (fun x : ℝ => (x, ψ x)) (Set.Ioo (-B₁) B₁) :=
      continuousOn_id.prodMk hψ
    refine hp.mono ?_
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [Set.mem_Ioo]
    have hxabs : |x| ≤ R₁ := abs_le.mpr ⟨hx.1, le_trans hx.2 hR₁pos.le⟩
    exact ⟨by linarith [hR₁_lt_B₁, (abs_le.mp hxabs).1], by linarith [hR₁_lt_B₁, hB₁, hx.2]⟩
  have hinj₁ : Set.InjOn γ₁ (Set.Icc (-R₂) 0) := by
    intro y₁ _ y₂ _ h
    exact congrArg Prod.snd h
  have hinj₂ : Set.InjOn γ₂ (Set.Icc (-R₁) 0) := by
    intro x₁ _ x₂ _ h
    exact congrArg Prod.fst h
  have hγ0 : γ₁ 0 = γ₂ 0 := by
    show (φ 0, (0 : ℝ)) = ((0 : ℝ), ψ 0)
    rw [hφ0, hψ0]
  have hdisj : γ₁ '' Set.Icc (-R₂) 0 ∩ γ₂ '' Set.Icc (-R₁) 0 = {γ₁ 0} := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz1, hz2⟩ := hz
      obtain ⟨y, hy, hyz⟩ := hz1
      obtain ⟨x, hx, hxz⟩ := hz2
      have hγeq : γ₁ y = γ₂ x := by rw [hyz, hxz]
      have hy_eq : y = ψ x := by
        simpa [hγ₁def, hγ₂def] using congrArg Prod.snd hγeq
      have hx_eq : x = φ y := by
        simpa [hγ₁def, hγ₂def] using (congrArg Prod.fst hγeq).symm
      have hyabs : |y| ≤ R₂ := abs_le.mpr ⟨hy.1, le_trans hy.2 hR₂pos.le⟩
      have hxabs : |x| ≤ R₁ := abs_le.mpr ⟨hx.1, le_trans hx.2 hR₁pos.le⟩
      have h1 : |y| ≤ |y| / 4 := by
        have h2 : |ψ x| ≤ |x| / 2 := hψs x (le_trans hxabs hR₁_le_B₁)
        have h3 : |φ y| ≤ |y| / 2 := hφs y (le_trans hyabs hR₂_le_A₂)
        calc |y| = |ψ x| := by rw [hy_eq]
          _ ≤ |x| / 2 := h2
          _ = |φ y| / 2 := by rw [hx_eq]
          _ ≤ (|y| / 2) / 2 := by linarith
          _ = |y| / 4 := by ring
      have hy0 : y = 0 := by
        have h2 : |y| = 0 := by linarith [abs_nonneg y]
        exact abs_eq_zero.mp h2
      rw [Set.mem_singleton_iff]
      have hγ : γ₁ y = γ₁ 0 := by
        show (φ y, y) = (φ 0, (0 : ℝ))
        rw [hy0, hφ0]
      rw [← hyz]
      exact hγ
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [Set.mem_inter_iff]
      refine ⟨⟨0, ⟨by linarith [hR₂pos], le_refl 0⟩, ?_⟩,
              ⟨0, ⟨by linarith [hR₁pos], le_refl 0⟩, ?_⟩⟩
      · show γ₁ 0 = z
        rw [hz]
      · show γ₂ 0 = z
        rw [hz, hγ0]
  refine ⟨V, hVopen, h0V, ?_⟩
  rw [hmain]
  exact two_arcs_glue hR₂pos hR₁pos hcont₁ hcont₂ hinj₁ hinj₂ hγ0 hdisj

/-- **The straightened model**: `C¹` functions with `fderiv fᵢ 0 = fst` and `fderiv g 0 = snd`.
The family maximum and the transverse function are fed into `isLocallyArc_of_family_data` using
`family_max_graph_slope` and `graph_snd_slope`. -/
theorem isLocallyArc_max_family_of_straight {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ι → ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hf0 : ∀ i, f i 0 = 0)
    (hdf : ∀ i, fderiv ℝ (f i) 0 = ContinuousLinearMap.fst ℝ ℝ ℝ)
    (hg : ContDiff ℝ 1 g) (hg0 : g 0 = 0)
    (hdg : fderiv ℝ g 0 = ContinuousLinearMap.snd ℝ ℝ ℝ) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (0 : ℝ × ℝ) ∈ V ∧
      Work.Smooth.SphereJordan.IsLocallyArc
        ↥(V ∩ {q : ℝ × ℝ |
          max (Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i q)) (g q) = 0}) := by
  obtain ⟨A₁, A₂, hA₁, hA₂, φ, hφ0, hφc, hφs, hφcond⟩ :=
    family_max_graph_slope hf hf0 hdf
  obtain ⟨B₁, B₂, ρ, hB₁, hB₂, hρ, ψ, hψ0, hψc, hψs, hψcond, hglin⟩ :=
    graph_snd_slope hg hg0 hdg
  exact isLocallyArc_of_family_data hA₁ hA₂ hB₁ hB₂ hρ hφc hφ0 hφs hψc hψ0 hψs
    (fun x y hx hy => hφcond x y hx hy) (fun x y hx hy => hψcond x y hx hy) hglin


theorem isLocallyArc_max_family_common_derivative {ι : Type*} [Fintype ι] [Nonempty ι]
    {ψ : ι → ℝ × ℝ → ℝ} {G : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {D : (ℝ × ℝ) →L[ℝ] ℝ}
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (hG : ContDiff ℝ 1 G)
    (hψp : ∀ i, ψ i p = 0) (hGp : G p = 0)
    (hdψ : ∀ i, fderiv ℝ (ψ i) p = D) (hD : D ≠ 0)
    (hGind : ∀ t : ℝ, fderiv ℝ G p ≠ t • D) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧
      Work.Smooth.SphereJordan.IsLocallyArc
        ↥(V ∩ {q : ℝ × ℝ |
          max (Finset.sup' Finset.univ Finset.univ_nonempty (fun i => ψ i q)) (G q) = 0}) := by
  set a₁ : ℝ := D (1, 0) with ha₁
  set b₁ : ℝ := D (0, 1) with hb₁
  set a₂ : ℝ := (fderiv ℝ G p) (1, 0) with ha₂
  set b₂ : ℝ := (fderiv ℝ G p) (0, 1) with hb₂
  have hDapp : ∀ z : ℝ × ℝ, D z = a₁ * z.1 + b₁ * z.2 := by
    intro z
    rw [ha₁, hb₁]
    exact clm_apply_eq D z
  have hGapp : ∀ z : ℝ × ℝ, (fderiv ℝ G p) z = a₂ * z.1 + b₂ * z.2 := by
    intro z
    rw [ha₂, hb₂]
    exact clm_apply_eq (fderiv ℝ G p) z
  have hD_ne : a₁ ≠ 0 ∨ b₁ ≠ 0 := by
    by_contra hcon
    have h1 : a₁ = 0 := by
      by_contra h
      exact hcon (Or.inl h)
    have h2 : b₁ = 0 := by
      by_contra h
      exact hcon (Or.inr h)
    exact hD (ContinuousLinearMap.ext fun z => by rw [hDapp z, h1, h2]; simp)
  have hdet : a₁ * b₂ - a₂ * b₁ ≠ 0 := by
    intro hd
    rcases eq_or_ne a₁ 0 with ha | ha
    · have hb : b₁ ≠ 0 := by
        rcases hD_ne with h | h
        · exact absurd ha h
        · exact h
      have ha₂0 : a₂ = 0 := by
        have h : a₁ * b₂ - a₂ * b₁ = -(a₂ * b₁) := by rw [ha]; ring
        rw [h] at hd
        exact (mul_eq_zero.mp (neg_eq_zero.mp hd)).resolve_right hb
      refine hGind (b₂ / b₁) (ContinuousLinearMap.ext fun z => ?_)
      rw [hGapp z, smul_apply, smul_eq_mul, hDapp z, ha, ha₂0]
      field_simp
      ring
    · have hb₂eq : b₂ = a₂ * b₁ / a₁ := by
        rw [eq_div_iff ha]
        nlinarith [hd]
      refine hGind (a₂ / a₁) (ContinuousLinearMap.ext fun z => ?_)
      rw [hGapp z, smul_apply, smul_eq_mul, hDapp z, hb₂eq]
      field_simp
  -- the pair of functionals is injective
  have hkerL : ∀ z : ℝ × ℝ, (D.prod (fderiv ℝ G p)) z = 0 → z = 0 := by
    intro z hz
    have h1 : D z = 0 := by
      have := congrArg Prod.fst hz
      simpa [ContinuousLinearMap.prod_apply] using this
    have h2 : (fderiv ℝ G p) z = 0 := by
      have := congrArg Prod.snd hz
      simpa [ContinuousLinearMap.prod_apply] using this
    have hz1 : z.1 = 0 := by
      have h : b₂ * D z - b₁ * ((fderiv ℝ G p) z) = 0 := by rw [h1, h2]; ring
      rw [hDapp z, hGapp z] at h
      have h' : (a₁ * b₂ - a₂ * b₁) * z.1 = 0 := by
        have hh := h
        ring_nf at hh ⊢
        linarith
      exact (mul_eq_zero.mp h').resolve_left hdet
    have hz2 : z.2 = 0 := by
      have h : a₁ * ((fderiv ℝ G p) z) - a₂ * D z = 0 := by rw [h1, h2]; ring
      rw [hDapp z, hGapp z] at h
      have h' : (a₁ * b₂ - a₂ * b₁) * z.2 = 0 := by
        have hh := h
        ring_nf at hh ⊢
        linarith
      exact (mul_eq_zero.mp h').resolve_left hdet
    exact Prod.ext hz1 hz2
  have hinj : Function.Injective (((D.prod (fderiv ℝ G p))) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) := by
    intro z1 z2 hz
    have hz' : ((D.prod (fderiv ℝ G p)) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (z1 - z2) = 0 := by
      rw [map_sub, hz, sub_self]
    have h0 := hkerL (z1 - z2) hz'
    exact sub_eq_zero.mp h0
  have hker : (((D.prod (fderiv ℝ G p))) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hsurj : Function.Surjective (((D.prod (fderiv ℝ G p))) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hrange : (((D.prod (fderiv ℝ G p))) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.ofBijective (D.prod (fderiv ℝ G p)) hker hrange
  have he : ∀ z : ℝ × ℝ, e z = (D z, (fderiv ℝ G p) z) := by
    intro z
    have h : (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = D.prod (fderiv ℝ G p) :=
      ContinuousLinearEquiv.coe_ofBijective (D.prod (fderiv ℝ G p)) hker hrange
    have h2 := congrArg (fun (f : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) => f z) h
    simpa [ContinuousLinearMap.prod_apply] using h2
  set M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (e.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) with hM
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  { toFun := fun z => p + M z
    invFun := fun q => e (q - p)
    left_inv := fun z => by
      show e ((p + M z) - p) = z
      rw [add_sub_cancel_left]
      show e (e.symm z) = z
      exact ContinuousLinearEquiv.apply_symm_apply e z
    right_inv := fun q => by
      show p + M (e (q - p)) = q
      have h : M (e (q - p)) = q - p := by
        show (e.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e (q - p)) = q - p
        exact ContinuousLinearEquiv.symm_apply_apply e (q - p)
      rw [h, add_sub_cancel]
    continuous_toFun := continuous_const.add M.continuous
    continuous_invFun := e.continuous.comp (continuous_id.sub continuous_const) }
  have hHapply : ∀ z : ℝ × ℝ, H z = p + M z := fun z => rfl
  have hMcd : ContDiff ℝ 1 (fun z : ℝ × ℝ => M z) := ContinuousLinearMap.contDiff M
  have hHcd : ContDiff ℝ 1 (fun z : ℝ × ℝ => p + M z) :=
    (contDiff_const (c := p)).add hMcd
  have hfcd : ∀ i, ContDiff ℝ 1 (fun z : ℝ × ℝ => ψ i (p + M z)) :=
    fun i => (hψ i).comp hHcd
  have hf0 : ∀ i, (fun z : ℝ × ℝ => ψ i (p + M z)) 0 = 0 := by
    intro i
    show ψ i (p + M 0) = 0
    rw [map_zero, add_zero]
    exact hψp i
  have hdf : ∀ i, fderiv ℝ (fun z : ℝ × ℝ => ψ i (p + M z)) 0
      = ContinuousLinearMap.fst ℝ ℝ ℝ := by
    intro i
    rw [Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear (ψ i) (hψ i) p M, hdψ i]
    refine ContinuousLinearMap.ext fun z => ?_
    have h3 : (D (M z), (fderiv ℝ G p) (M z)) = z := by
      rw [← he (M z)]
      show e (e.symm z) = z
      exact ContinuousLinearEquiv.apply_symm_apply e z
    simpa using congrArg Prod.fst h3
  have hgcd : ContDiff ℝ 1 (fun z : ℝ × ℝ => G (p + M z)) := hG.comp hHcd
  have hg0 : (fun z : ℝ × ℝ => G (p + M z)) 0 = 0 := by
    show G (p + M 0) = 0
    rw [map_zero, add_zero]
    exact hGp
  have hdg : fderiv ℝ (fun z : ℝ × ℝ => G (p + M z)) 0
      = ContinuousLinearMap.snd ℝ ℝ ℝ := by
    rw [Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear G hG p M]
    refine ContinuousLinearMap.ext fun z => ?_
    have h3 : (D (M z), (fderiv ℝ G p) (M z)) = z := by
      rw [← he (M z)]
      show e (e.symm z) = z
      exact ContinuousLinearEquiv.apply_symm_apply e z
    simpa using congrArg Prod.snd h3
  obtain ⟨V, hVopen, h0V, hloc⟩ :=
    isLocallyArc_max_family_of_straight hfcd hf0 hdf hgcd hg0 hdg
  refine ⟨H '' V, H.isOpenMap V hVopen, ?_, ?_⟩
  · refine ⟨0, h0V, ?_⟩
    show H 0 = p
    rw [hHapply, map_zero, add_zero]
  · refine Work.Smooth.OneManifold.isLocallyArc_of_image_eq H ?_ hloc
    ext q
    constructor
    · rintro ⟨z, ⟨hzV, hzZ⟩, rfl⟩
      exact ⟨⟨z, hzV, rfl⟩, hzZ⟩
    · rintro ⟨⟨z, hzV, hzq⟩, hqZ⟩
      refine ⟨z, ⟨hzV, ?_⟩, hzq⟩
      show max (Finset.sup' Finset.univ Finset.univ_nonempty (fun i => ψ i (p + M z)))
        (G (p + M z)) = 0
      have h := hqZ
      rw [← hzq] at h
      simpa only [hHapply z, Set.mem_ofPred_eq] using h

end Work.Drive.Mono
