import Mathlib
import Submission.Work.RPB.B1a.exists_bounded_component_compl
import Submission.Work.RPB.B1a.eq_of_isBounded_component_compl
import Submission.Work.RPB1a.Caratheodory.Brouwer.frontier_component_eq_of_bounded
import Submission.Work.RPB.Port.Drive.isPathConnected_exterior

set_option autoImplicit false

open Complex Set Metric
open scoped Topology

/-!
# Jordan–Brouwer separation of the plane by a subset homeomorphic to the circle

If `J ⊆ ℂ` is homeomorphic to the circle, then its complement is the disjoint union of a bounded
open preconnected piece `ins` and an unbounded open preconnected piece `out`, and both have `J`
as frontier.

The proof parametrises `J` by a continuous injective `γ : Circle → ℂ`, transports to `ℝ × ℝ`
along the linear homeomorphism `ℂ ≃L[ℝ] ℝ × ℝ`, takes `ins` to be the unique bounded component of
the complement of `range γ` (existence and uniqueness are
`Work.RPB.B1a.exists_bounded_component_compl` and
`Work.RPB.B1a.eq_of_isBounded_component_compl`), takes `out` to be the complementary component
through a point far outside, and transports back.  The frontier facts come from
`Work.RPB1a.Caratheodory.Brouwer.frontier_component_eq_of_bounded`.
-/

namespace Work.RPB.B1a

theorem jordan_separation_plane (J : Set ℂ) (hJ : Nonempty (J ≃ₜ Circle)) :
    ∃ ins out : Set ℂ, IsOpen ins ∧ IsOpen out ∧ IsPreconnected ins ∧ IsPreconnected out ∧
      Bornology.IsBounded ins ∧ ¬ Bornology.IsBounded out ∧
      Jᶜ = ins ∪ out ∧ Disjoint ins out ∧ frontier ins = J ∧ frontier out = J := by
  obtain ⟨e⟩ := hJ
  set γ : Circle → ℂ := fun z => ((e.symm z : J) : ℂ) with hγdef
  have hγcont : Continuous γ := continuous_subtype_val.comp e.symm.continuous
  have hinjγ : Function.Injective γ := fun x y h => e.symm.injective (Subtype.ext h)
  have hrangeγ : Set.range γ = J := by
    ext z; constructor
    · rintro ⟨w, rfl⟩; exact (e.symm w).2
    · intro hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      show ((e.symm (e ⟨z, hz⟩) : J) : ℂ) = z
      rw [e.symm_apply_apply]
  set γR : Circle → ℝ × ℝ := fun z => Complex.equivRealProdCLM (γ z) with hγRdef
  have hγRcont : Continuous γR := Complex.equivRealProdCLM.continuous.comp hγcont
  have hγRinj : Function.Injective γR :=
    fun x y h => hinjγ (Complex.equivRealProdCLM.injective h)
  have hcomp' : (fun x : ℂ => Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x)) = id := by
    funext x; exact ContinuousLinearEquiv.symm_apply_apply _ x
  have hsymm : Complex.equivRealProdCLM.symm '' Set.range γR = Set.range γ := by
    have hr : Set.range γR = Complex.equivRealProdCLM '' Set.range γ := by
      change Set.range (Complex.equivRealProdCLM ∘ γ) = Complex.equivRealProdCLM '' Set.range γ
      rw [Set.range_comp]
    rw [hr, Set.image_image, hcomp', Set.image_id]
  have hKclosed : IsClosed (Set.range γR) := (isCompact_range hγRcont).isClosed
  have hKbdd : Bornology.IsBounded (Set.range γR) := (isCompact_range hγRcont).isBounded
  obtain ⟨x₀, hx₀, hbd₀⟩ := Work.RPB.B1a.exists_bounded_component_compl γR hγRcont hγRinj
  have huniq := Work.RPB.B1a.eq_of_isBounded_component_compl γR hγRcont hγRinj ⟨x₀, hx₀, hbd₀⟩
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mp hKbdd
  set R : ℝ := max R₀ 1 with hRdef
  have hRnn : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hKR : Set.range γR ⊆ Metric.ball (0 : ℝ × ℝ) R := fun x hx =>
    Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp (hR₀ hx)) (le_max_left _ _))
  set t : ℝ × ℝ := (R + 1, 0) with htdef
  have htE : R ≤ dist t 0 := by
    rw [htdef, Work.RPB.Port.Drive.dist_prod_zero]
    simp only [Prod.snd, abs_zero]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1),
      max_eq_left (by linarith : (0 : ℝ) ≤ R + 1)]
    linarith
  have htp : t ∈ (Set.range γR)ᶜ := by
    rw [Set.mem_compl_iff]
    intro htK
    have h1 : dist t 0 < R := Metric.mem_ball.mp (hKR htK)
    linarith
  set G : Set (ℝ × ℝ) := (Set.range γR)ᶜ with hGdef
  have hGopen : IsOpen G := hKclosed.isOpen_compl
  have hEpc : IsPathConnected {z : ℝ × ℝ | R ≤ dist z 0} :=
    Work.RPB.Port.Drive.isPathConnected_exterior R hRnn
  have hEsub : {z : ℝ × ℝ | R ≤ dist z 0} ⊆ G := by
    intro z hz hzK
    simp only [Set.mem_ofPred_eq] at hz
    have h1 : dist z 0 < R := Metric.mem_ball.mp (hKR hzK)
    linarith
  set C₁ : Set (ℝ × ℝ) := connectedComponentIn G x₀ with hC₁def
  set C₂ : Set (ℝ × ℝ) := connectedComponentIn G t with hC₂def
  have hx₀G : x₀ ∈ G := by rw [hGdef, Set.mem_compl_iff]; exact hx₀
  have htG : t ∈ G := by rw [hGdef]; exact htp
  have hC₁bdd : Bornology.IsBounded C₁ := by rw [hC₁def]; exact hbd₀
  have hEC₂ : {z : ℝ × ℝ | R ≤ dist z 0} ⊆ C₂ :=
    hEpc.isConnected.isPreconnected.subset_connectedComponentIn htE hEsub
  have hC₂unbdd : ¬ Bornology.IsBounded C₂ := by
    intro hb
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mp hb
    obtain ⟨n, hn⟩ : ∃ n : ℕ, r ≤ (n : ℝ) := ⟨Nat.ceil r, Nat.le_ceil r⟩
    have hmem' : ((R + (n : ℝ) + 1 : ℝ), (0 : ℝ)) ∈ Metric.ball (0 : ℝ × ℝ) r := by
      apply hr
      apply hEC₂
      show R ≤ dist ((R + (n : ℝ) + 1 : ℝ), (0 : ℝ)) 0
      rw [Work.RPB.Port.Drive.dist_prod_zero]
      simp only [Prod.snd, abs_zero]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R + (n : ℝ) + 1),
        max_eq_left (by positivity : (0 : ℝ) ≤ R + (n : ℝ) + 1)]
      linarith
    have hd : dist ((R + (n : ℝ) + 1 : ℝ), (0 : ℝ)) 0 < r := Metric.mem_ball.mp hmem'
    have hd' : dist ((R + (n : ℝ) + 1 : ℝ), (0 : ℝ)) 0 = R + (n : ℝ) + 1 := by
      rw [Work.RPB.Port.Drive.dist_prod_zero]
      simp only [Prod.snd, abs_zero]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R + (n : ℝ) + 1),
        max_eq_left (by positivity : (0 : ℝ) ≤ R + (n : ℝ) + 1)]
    rw [hd'] at hd
    linarith
  have hkey : ∀ y ∈ G, connectedComponentIn G y = C₁ ∨ connectedComponentIn G y = C₂ := by
    intro y hy
    by_cases hb : Bornology.IsBounded (connectedComponentIn G y)
    · left
      rw [hC₁def]
      exact huniq y x₀ (by simpa [hGdef] using hy) hx₀ (by simpa [hGdef] using hb) hbd₀
    · right
      have hnot : ¬ ∃ r : ℝ, connectedComponentIn G y ⊆ Metric.ball (0 : ℝ × ℝ) r :=
        fun hcon => hb ((Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mpr hcon)
      have hnot' : ¬ (connectedComponentIn G y ⊆ Metric.ball (0 : ℝ × ℝ) R) :=
        fun hsub => hnot ⟨R, hsub⟩
      obtain ⟨z, hzmem, hzout⟩ := Set.not_subset.mp hnot'
      have hzE : R ≤ dist z 0 := le_of_not_gt fun h => hzout (Metric.mem_ball.mpr h)
      have hzC₂ : z ∈ C₂ := hEC₂ hzE
      rw [hC₂def] at hzC₂ ⊢
      have h1 : connectedComponentIn G y = connectedComponentIn G z :=
        connectedComponentIn_eq hzmem
      have h2 : connectedComponentIn G z = connectedComponentIn G t :=
        (connectedComponentIn_eq hzC₂).symm
      exact h1.trans h2
  have hCne : C₁ ≠ C₂ := by
    intro heq
    exact hC₂unbdd (heq ▸ hC₁bdd)
  have hdisj : Disjoint C₁ C₂ := by
    rw [Set.disjoint_left]
    intro w hw₁ hw₂
    rw [hC₁def] at hw₁
    rw [hC₂def] at hw₂
    have h1 : connectedComponentIn G x₀ = connectedComponentIn G w := connectedComponentIn_eq hw₁
    have h2 : connectedComponentIn G t = connectedComponentIn G w := connectedComponentIn_eq hw₂
    exact hCne (hC₁def ▸ hC₂def ▸ (h1.trans h2.symm))
  have hcover : C₁ ∪ C₂ = G := by
    ext y
    constructor
    · intro hy
      rcases hy with h | h
      · rw [hC₁def] at h; exact connectedComponentIn_subset G x₀ h
      · rw [hC₂def] at h; exact connectedComponentIn_subset G t h
    · intro hy
      rcases hkey y hy with h | h
      · left; rw [← h]; exact mem_connectedComponentIn hy
      · right; rw [← h]; exact mem_connectedComponentIn hy
  have hopen₁ : IsOpen C₁ := by rw [hC₁def]; exact hGopen.connectedComponentIn
  have hopen₂ : IsOpen C₂ := by rw [hC₂def]; exact hGopen.connectedComponentIn
  have hpc₁ : IsPreconnected C₁ := by rw [hC₁def]; exact isPreconnected_connectedComponentIn
  have hpc₂ : IsPreconnected C₂ := by rw [hC₂def]; exact isPreconnected_connectedComponentIn
  have hbd' : ∃ x : ℝ × ℝ, x ∉ Set.range γR ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γR)ᶜ) x) := ⟨x₀, hx₀, hbd₀⟩
  have hfront₁ : frontier C₁ = Set.range γR := by
    rw [hC₁def, hGdef]
    exact Work.RPB1a.Caratheodory.Brouwer.frontier_component_eq_of_bounded γR hγRcont hγRinj
      hbd' x₀ hx₀
  have hfront₂ : frontier C₂ = Set.range γR := by
    rw [hC₂def, hGdef]
    exact Work.RPB1a.Caratheodory.Brouwer.frontier_component_eq_of_bounded γR hγRcont hγRinj
      hbd' t (by rw [hGdef] at htG; exact htG)
  have hsymm_img (s : Set (ℝ × ℝ)) :
      Complex.equivRealProdCLM.symm '' s = Complex.equivRealProdCLM ⁻¹' s := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx
      exact ⟨Complex.equivRealProdCLM x, hx, ContinuousLinearEquiv.symm_apply_apply _ x⟩
  have hcomp'' : (fun x : ℝ × ℝ => Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm x))
      = id := by
    funext x; exact ContinuousLinearEquiv.apply_symm_apply _ x
  refine ⟨Complex.equivRealProdCLM.symm '' C₁, Complex.equivRealProdCLM.symm '' C₂,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsymm_img C₁]; exact hopen₁.preimage Complex.equivRealProdCLM.continuous
  · rw [hsymm_img C₂]; exact hopen₂.preimage Complex.equivRealProdCLM.continuous
  · exact hpc₁.image _ Complex.equivRealProdCLM.symm.continuous.continuousOn
  · exact hpc₂.image _ Complex.equivRealProdCLM.symm.continuous.continuousOn
  · exact Complex.equivRealProdCLM.symm.lipschitzWith.isBounded_image hC₁bdd
  · intro hb
    have h1 : Bornology.IsBounded
        (Complex.equivRealProdCLM '' (Complex.equivRealProdCLM.symm '' C₂)) :=
      Complex.equivRealProdCLM.lipschitzWith.isBounded_image hb
    have himg : Complex.equivRealProdCLM '' (Complex.equivRealProdCLM.symm '' C₂) = C₂ := by
      rw [Set.image_image, hcomp'', Set.image_id]
    rw [himg] at h1
    exact hC₂unbdd h1
  · have key : Complex.equivRealProdCLM.symm '' C₁ ∪ Complex.equivRealProdCLM.symm '' C₂
        = (Set.range γ)ᶜ := by
      rw [← Set.image_union, hcover, hGdef,
        Set.image_compl_eq Complex.equivRealProdCLM.symm.bijective, hsymm]
    rw [← hrangeγ]
    exact key.symm
  · rw [Set.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨a, ha, hxa⟩ := hx₁
    obtain ⟨b, hb, hxb⟩ := hx₂
    have hab : a = b := Complex.equivRealProdCLM.symm.injective (hxa.trans hxb.symm)
    subst hab
    exact (Set.disjoint_left.mp hdisj ha) hb
  · have h := Homeomorph.image_frontier (Complex.equivRealProdCLM.symm.toHomeomorph) C₁
    rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
    rw [← h, hfront₁, hsymm, hrangeγ]
  · have h := Homeomorph.image_frontier (Complex.equivRealProdCLM.symm.toHomeomorph) C₂
    rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
    rw [← h, hfront₂, hsymm, hrangeγ]

end Work.RPB.B1a
