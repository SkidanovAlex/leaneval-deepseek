import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_end
import Submission.Work.L62.stab_hyp
import Submission.Work.L62.fin_sep
import Submission.Work.L62.collar_radius
import Submission.Work.L62.cover_extract
import Submission.Work.L62.tail_of_branch
import Submission.Work.L62.avail_up
import Submission.Work.L62.avail_down

/-!
# L62 — the assembly of Shishikura's Lemma 6.2 (`Work.L62.l62c`)

This file reduces `L62Statement` to the two geometric inputs proved elsewhere:

* `Work.L62.tail_uniform2` — the deep tail of the chain (both ends, via the sign `s`);
* `Work.L62.head_package` — the finite head of the chain, uniformly over a neighbourhood of a
  parameter `β` (it consumes `Work.L62.StabHyp d`, which is `Work.L62.head_stability`).

Everything in between — the end choice `exists_uniform_drift`, the finite cover of the parameter
box `cover_extract`, the splicing of the head and the tail, the contract's conjunction — is done
here.  See `NOTES_L62_FINAL.md`.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

set_option maxHeartbeats 4000000

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- The parameter box of Lemma 6.2: one period `0 ≤ Re β ≤ 1` and `|Im β| ≤ b`. -/
theorem isCompact_box_l62 (b : ℝ) :
    IsCompact {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
  have himg : ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-b) b))
      = {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
    ext β
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := hp
      refine ⟨by simpa using hp1.1, by simpa using hp1.2, ?_⟩
      have h2 : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
      rw [h2]
      exact abs_le.mpr ⟨hp2.1, hp2.2⟩
    · intro hβ
      refine ⟨(β.re, β.im), ⟨⟨hβ.1, hβ.2.1⟩, ?_⟩, ?_⟩
      · exact abs_le.mp hβ.2.2
      · simp
  rw [← himg]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-- The set of parameters `β` of the box for which the *upper* end is available with drift `≥ κ`. -/
def upBox (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (b κ : ℝ) : Set ℂ :=
  {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b ∧ AvailableUp d hd β ∧ κ ≤ β.im}

/-- The set of parameters `β` of the box for which the *lower* end is available with drift `≥ κ`. -/
def dnBox (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (b κ : ℝ)
    (cl : ℂ) : Set ℂ :=
  {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b ∧ AvailableDown d hd β ∧ κ ≤ cl.im - β.im}

theorem isCompact_upBox (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d)
    {b κ : ℝ} (hb : 0 < b) : IsCompact (upBox d hd b κ) := by
  have h1 : upBox d hd b κ = {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
      {β : ℂ | AvailableUp d hd β} ∩ {β : ℂ | κ ≤ β.im} := by
    ext β
    simp only [upBox, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [h1]
  exact (isCompact_box_l62 b).inter_right (isClosed_availableUp d hd) |>.inter_right
    (isClosed_le continuous_const Complex.continuous_im)

theorem isCompact_dnBox (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d)
    {b κ : ℝ} (hb : 0 < b) {cl : ℂ} : IsCompact (dnBox d hd b κ cl) := by
  have h1 : dnBox d hd b κ cl = {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
      {β : ℂ | AvailableDown d hd β} ∩ {β : ℂ | β.im ≤ cl.im - κ} := by
    ext β
    simp only [dnBox, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨⟨⟨h1, h2, h3⟩, h4⟩, by linarith⟩
    · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩
      exact ⟨h1, h2, h3, h4, by linarith⟩
  rw [h1]
  exact (isCompact_box_l62 b).inter_right (isClosed_availableDown d hd) |>.inter_right
    (isClosed_le Complex.continuous_im continuous_const)

/-- The head data attached to a parameter `β` of one of the two boxes: the point chain's crossing
index `j₀`, the cover radius `ε`, the disc radius bound `ρ₁`, the derivative bounds `C, C'` and the
compact collar `A` of `Work.L62.head_package`. -/
structure HeadDatum (d : MandelDim.ParabData g₀ D) (Y κ : ℝ) (ζa ζb β : ℂ) (s : ℝ) where
  ζ : ℂ
  j₀ : ℕ
  ρ₁ : ℝ
  ε : ℝ
  δ : ℝ
  C : ℝ
  C' : ℝ
  A : Set ℂ
  hζ : ζ = ζa ∨ ζ = ζb
  hj₀ : 0 < j₀
  hρ₁ : 0 < ρ₁
  hρκ : ρ₁ < κ / 16
  hρ48 : ρ₁ < 1 / 48
  hε : 0 < ε
  hδ : 0 < δ
  hC : 0 < C
  hC' : 0 < C'
  hAc : IsCompact A
  hADE : A ⊆ d.DE
  hmain : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → ∀ β' : ℂ, ‖β' - β‖ < ε →
    ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → A ⊆ DR → DifferentiableOn ℂ R DR →
      (∀ w ∈ A, ‖R w - d.E w‖ < δ) →
      ∃ W : ℕ → Set ℂ, W 0 = Metric.ball ζ ρ ∧
        (∀ j, j ≤ j₀ → IsOpen (W j) ∧ IsConnected (W j) ∧ Bornology.IsBounded (W j) ∧
          Metric.diam (W j) < 1 / 2) ∧
        (∀ j, j < j₀ → W (j + 1) ⊆ A ∧
          Set.InjOn (fun w => R w - β') (W (j + 1)) ∧
          (fun w => R w - β') '' W (j + 1) = W j ∧
          (∀ u ∈ W (j + 1), C < ‖deriv ((fun u => R u - β')^[j + 1]) u‖ ∧
            ‖deriv ((fun u => R u - β')^[j + 1]) u‖ < C')) ∧
        (∀ i j, i ≤ j₀ → j ≤ j₀ → i ≠ j →
          Disjoint (MandelDim.piExp '' W i) (MandelDim.piExp '' W j)) ∧
        (∀ w ∈ W j₀, Y < s * w.im) ∧
        (∀ j, j < j₀ → ∀ w ∈ W j, s * w.im < Y + κ / 8) ∧
        Metric.diam (W j₀) ≤ 1 / 24 ∧ 3 * Metric.diam (W j₀) < κ / 4

/-- The tail input of the assembly: `Work.L62.tail_uniform2`'s statement with `κ`, `cl` as the
leading arguments. -/
def TailHyp (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (b : ℝ) : Prop :=
  ∀ (κ : ℝ) (cl : ℂ), 0 < κ →
    Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl) →
    ∃ (Y δt C₀ C₂ C₂' : ℝ), d.η₀ + 2 < Y ∧ 0 < δt ∧ 0 < C₀ ∧ 0 < C₂ ∧ 0 < C₂' ∧
      ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → ∀ s : ℝ,
        ((s = 1 ∧ AvailableUp d hd β ∧ κ ≤ β.im) ∨
          (s = -1 ∧ AvailableDown d hd β ∧ κ ≤ cl.im - β.im)) →
        ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → MandelDim.IsTEquivariantOn R DR →
          DifferentiableOn ℂ R DR → {w : ℂ | Y - 1 ≤ |w.im|} ⊆ DR →
          (∀ w : ℂ, Y - 1 ≤ |w.im| → ‖R w - d.E w‖ < δt) →
          ∀ W₀ : Set ℂ, IsOpen W₀ → IsConnected W₀ → Bornology.IsBounded W₀ →
            Metric.diam W₀ ≤ 1 / 24 → 3 * Metric.diam W₀ < κ / 4 →
            (∀ u ∈ W₀, Y < s * u.im) →
            ∃ V : ℕ → Set ℂ, V 0 = W₀ ∧ ∀ j : ℕ,
              IsOpen (V j) ∧ IsConnected (V j) ∧ V (j + 1) ⊆ DR ∧
              Set.InjOn (fun u => R u - β) (V (j + 1)) ∧
              (fun u => R u - β) '' V (j + 1) = V j ∧
              (∀ u ∈ V j, Y + (j : ℝ) * κ / 8 < s * u.im) ∧
              Bornology.IsBounded (V j) ∧ Metric.diam (V j) < 1 / 2 ∧
              (∃ u ∈ V j, ∃ u' ∈ V (j + 1), ‖u - u'‖ < C₀) ∧
              (∀ i j : ℕ, i ≠ j → Disjoint (MandelDim.piExp '' V i) (MandelDim.piExp '' V j)) ∧
              (∀ u ∈ V j, C₂ < ‖deriv ((fun u => R u - β)^[j]) u‖ ∧
                ‖deriv ((fun u => R u - β)^[j]) u‖ < C₂')

/-- The head input of the assembly: for every admissible parameter `β` of the box, the head data
(`Work.L62.head_package`, which consumes `Work.L62.head_stability`). -/
def HeadHyp (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (b : ℝ)
    (ζa ζb : ℂ) : Prop :=
  ∀ (κ Y : ℝ) (cl : ℂ), 0 < κ → d.η₀ + 2 < Y →
    Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl) →
    ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → ∀ s : ℝ,
      ((s = 1 ∧ AvailableUp d hd β ∧ κ ≤ β.im) ∨
        (s = -1 ∧ AvailableDown d hd β ∧ κ ≤ cl.im - β.im)) →
      Nonempty (HeadDatum d Y κ ζa ζb β s)

/-! ## The derivative of an iterate splits at an intermediate time -/

theorem deriv_iterate_add {f : ℂ → ℂ} {m n : ℕ} {u : ℂ}
    (h1 : DifferentiableAt ℂ (f^[m]) ((f^[n]) u)) (h2 : DifferentiableAt ℂ (f^[n]) u) :
    deriv (f^[m+n]) u = deriv (f^[m]) ((f^[n]) u) * deriv (f^[n]) u := by
  have hfun : (f^[m+n]) = (f^[m]) ∘ (f^[n]) :=
    funext (fun x => Function.iterate_add_apply f m n x)
  rw [hfun]
  exact deriv_comp u h1 h2

/-- **The assembly of Lemma 6.2.**  `L62Statement`'s conclusion reduced to the tail
(`Work.L62.tail_uniform2`) and the head (`Work.L62.head_package`, consuming `StabHyp d`). -/
theorem l62c_aux {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) (b : ℝ) (hb : 0 < b)
    (ζa ζb : ℂ) (hζa : ζa ∉ d.DE) (hζb : ζb ∉ d.DE)
    (hsepab : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ))
    (hhead : HeadHyp d hd b ζa ζb) (htail : TailHyp d hd b) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : Set ℂ, IsCompact K ∧ K ⊆ d.DE ∧
      ∃ y₁ δ C₀ C₁ C₁' : ℝ, d.η₀ < y₁ ∧ 0 < δ ∧ 0 < C₁ ∧
        ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → MandelDim.IsTEquivariantOn R DR →
          DifferentiableOn ℂ R DR →
          K ∪ {w : ℂ | y₁ ≤ |w.im|} ⊆ DR →
          (∀ w ∈ K ∪ {w : ℂ | y₁ ≤ |w.im|}, ‖R w - d.E w‖ < δ) →
          ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
            ∃ (W : ℕ → Set ℂ) (s : ℝ), (s = 1 ∨ s = -1) ∧
              (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
              (∀ j, IsOpen (W j) ∧ IsConnected (W j)) ∧
              (∀ j, W (j + 1) ⊆ DR ∧ Set.InjOn (fun w => R w - β) (W (j + 1)) ∧
                (fun w => R w - β) '' W (j + 1) = W j) ∧
              (∀ i j, i ≠ j → Disjoint (MandelDim.piExp '' W i) (MandelDim.piExp '' W j)) ∧
              (∀ M : ℝ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ w ∈ W j, M < s * w.im) ∧
              (∀ j, Bornology.IsBounded (W j) ∧ Metric.diam (W j) < 1 / 2) ∧
              (∀ j, ∃ u ∈ W j, ∃ u' ∈ W (j + 1), ‖u - u'‖ < C₀) ∧
              (∀ j, ∀ w ∈ W j, C₁ < ‖deriv ((fun u => R u - β)^[j]) w‖ ∧
                ‖deriv ((fun u => R u - β)^[j]) w‖ < C₁') := by
  classical
  obtain ⟨cl, hcl⟩ := d.E_lower
  have hclim : 0 < cl.im := hd.cl_im_pos cl hcl
  have hup : ∀ β : ℂ, AvailableUp d hd β → 0 < β.im := fun β hβ => avail_up d hd hβ
  have hdn : ∀ β : ℂ, AvailableDown d hd β → β.im < cl.im := fun β hβ => avail_down d hd hcl hβ
  obtain ⟨κ, hκpos, hunif⟩ := exists_uniform_drift d hd hup hdn
  obtain ⟨Y, δt, C₀t, C₂, C₂', hYη, hδt, hC₀t, hC₂, hC₂', htailβ⟩ := htail κ cl hκpos hcl
  have hY1 : d.η₀ < Y - 1 := by linarith
  have hunit_up : ∀ β : ℂ, β ∈ upBox d hd b κ → Nonempty (HeadDatum d Y κ ζa ζb β 1) :=
    fun β hβ => hhead κ Y cl hκpos hYη hcl β hβ.1 hβ.2.1 hβ.2.2.1 1
      (Or.inl ⟨rfl, hβ.2.2.2.1, hβ.2.2.2.2⟩)
  have hunit_dn : ∀ β : ℂ, β ∈ dnBox d hd b κ cl → Nonempty (HeadDatum d Y κ ζa ζb β (-1)) :=
    fun β hβ => hhead κ Y cl hκpos hYη hcl β hβ.1 hβ.2.1 hβ.2.2.1 (-1)
      (Or.inr ⟨rfl, hβ.2.2.2.1, hβ.2.2.2.2⟩)
  let upD : (β : ℂ) → β ∈ upBox d hd b κ → HeadDatum d Y κ ζa ζb β 1 :=
    fun β hβ => Classical.choice (hunit_up β hβ)
  let dnD : (β : ℂ) → β ∈ dnBox d hd b κ cl → HeadDatum d Y κ ζa ζb β (-1) :=
    fun β hβ => Classical.choice (hunit_dn β hβ)
  have hminC : 0 < min (1 : ℝ) C₂ := lt_min one_pos hC₂
  let upε : ℂ → ℝ := fun β => if h : β ∈ upBox d hd b κ then (upD β h).ε else 1
  let upρ : ℂ → ℝ := fun β =>
    if h : β ∈ upBox d hd b κ then min (upD β h).ρ₁ ((upD β h).C * min 1 C₂ / 4) else 1
  let upδ : ℂ → ℝ := fun β =>
    if h : β ∈ upBox d hd b κ then min (upD β h).δ ((upD β h).C')⁻¹ else 1
  let upA : ℂ → Set ℂ := fun β => if h : β ∈ upBox d hd b κ then (upD β h).A else ∅
  let dnε : ℂ → ℝ := fun β => if h : β ∈ dnBox d hd b κ cl then (dnD β h).ε else 1
  let dnρ : ℂ → ℝ := fun β =>
    if h : β ∈ dnBox d hd b κ cl then min (dnD β h).ρ₁ ((dnD β h).C * min 1 C₂ / 4) else 1
  let dnδ : ℂ → ℝ := fun β =>
    if h : β ∈ dnBox d hd b κ cl then min (dnD β h).δ ((dnD β h).C')⁻¹ else 1
  let dnA : ℂ → Set ℂ := fun β => if h : β ∈ dnBox d hd b κ cl then (dnD β h).A else ∅
  have hupε : ∀ β ∈ upBox d hd b κ, 0 < upε β := by
    intro β hβ; simp only [upε, dif_pos hβ]; exact (upD β hβ).hε
  have hupρ : ∀ β ∈ upBox d hd b κ, 0 < upρ β := by
    intro β hβ; simp only [upρ, dif_pos hβ]
    exact lt_min (upD β hβ).hρ₁ (by have h1 := (upD β hβ).hC; have h2 := hminC; positivity)
  have hupδ : ∀ β ∈ upBox d hd b κ, 0 < upδ β := by
    intro β hβ; simp only [upδ, dif_pos hβ]
    exact lt_min (upD β hβ).hδ (by rw [inv_pos]; exact (upD β hβ).hC')
  have hupAc : ∀ β ∈ upBox d hd b κ, IsCompact (upA β) := by
    intro β hβ; simp only [upA, dif_pos hβ]; exact (upD β hβ).hAc
  have hupAB : ∀ β ∈ upBox d hd b κ, upA β ⊆ d.DE := by
    intro β hβ; simp only [upA, dif_pos hβ]; exact (upD β hβ).hADE
  have hdnε : ∀ β ∈ dnBox d hd b κ cl, 0 < dnε β := by
    intro β hβ; simp only [dnε, dif_pos hβ]; exact (dnD β hβ).hε
  have hdnρ : ∀ β ∈ dnBox d hd b κ cl, 0 < dnρ β := by
    intro β hβ; simp only [dnρ, dif_pos hβ]
    exact lt_min (dnD β hβ).hρ₁ (by have h1 := (dnD β hβ).hC; have h2 := hminC; positivity)
  have hdnδ : ∀ β ∈ dnBox d hd b κ cl, 0 < dnδ β := by
    intro β hβ; simp only [dnδ, dif_pos hβ]
    exact lt_min (dnD β hβ).hδ (by rw [inv_pos]; exact (dnD β hβ).hC')
  have hdnAc : ∀ β ∈ dnBox d hd b κ cl, IsCompact (dnA β) := by
    intro β hβ; simp only [dnA, dif_pos hβ]; exact (dnD β hβ).hAc
  have hdnAB : ∀ β ∈ dnBox d hd b κ cl, dnA β ⊆ d.DE := by
    intro β hβ; simp only [dnA, dif_pos hβ]; exact (dnD β hβ).hADE
  obtain ⟨t₁, ρ₀u, δ₀u, K₁, ht₁, hρ₀u, hδ₀u, hK₁c, hK₁B, hA₁K, hcov₁⟩ :=
    cover_extract (Λ := upBox d hd b κ) (isCompact_upBox d hd hb) hupε hupρ hupδ hupAc hupAB
  obtain ⟨t₂, ρ₀d, δ₀d, K₂, ht₂, hρ₀d, hδ₀d, hK₂c, hK₂B, hA₂K, hcov₂⟩ :=
    cover_extract (Λ := dnBox d hd b κ cl) (isCompact_dnBox d hd hb) hdnε hdnρ hdnδ hdnAc hdnAB
  refine ⟨min ρ₀u ρ₀d, lt_min hρ₀u hρ₀d, ?_⟩
  intro ρ hρ hρρ₀
  have hρu : ρ ≤ ρ₀u := le_trans hρρ₀ (min_le_left _ _)
  have hρd : ρ ≤ ρ₀d := le_trans hρρ₀ (min_le_right _ _)
  obtain ⟨MK, hMK⟩ : ∃ MK : ℝ, ∀ x ∈ K₁ ∪ K₂, ‖x‖ ≤ MK := by
    obtain ⟨MK, hMK⟩ := (hK₁c.union hK₂c).exists_bound_of_continuousOn continuous_norm.continuousOn
    exact ⟨MK, fun x hx => by simpa using hMK x hx⟩
  have hKbdd : Bornology.IsBounded (K₁ ∪ K₂) := (hK₁c.union hK₂c).isBounded
  set δ : ℝ := min (min δ₀u δ₀d) δt with hδdef
  set C₀ : ℝ := max C₀t (max (Metric.diam (K₁ ∪ K₂) + 1) (MK + max ‖ζa‖ ‖ζb‖ + 2)) with hC₀def
  set C₁ : ℝ := min (1 / 2 : ℝ) (ρ * min 1 C₂) with hC₁def
  set C₁' : ℝ := max 2 (max (δ₀u⁻¹ * max C₂' 1) (δ₀d⁻¹ * max C₂' 1)) with hC₁'def
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (lt_min hδ₀u hδ₀d) hδt
  have hC₁pos : 0 < C₁ := by
    rw [hC₁def]; exact lt_min (by norm_num) (mul_pos hρ hminC)
  have hδδu : δ ≤ δ₀u := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδδd : δ ≤ δ₀d := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδδt : δ ≤ δt := by rw [hδdef]; exact min_le_right _ _
  refine ⟨K₁ ∪ K₂, hK₁c.union hK₂c, fun w hw => by
    rcases hw with hw | hw
    · exact hK₁B hw
    · exact hK₂B hw, Y - 1, δ, C₀, C₁, C₁', hY1, hδpos, hC₁pos, ?_⟩
  intro R DR hDRo hTeq hRdiff hDRsub hclose
  have hDRsubY : {w : ℂ | Y - 1 ≤ |w.im|} ⊆ DR :=
    fun w hw => hDRsub (Or.inr hw)
  have hcloseY : ∀ w : ℂ, Y - 1 ≤ |w.im| → ‖R w - d.E w‖ < δt := by
    intro w hw
    exact lt_of_lt_of_le (hclose w (Or.inr hw)) hδδt
  have step : ∀ (s : ℝ) (Λ : Set ℂ) (εf ρf δf : ℂ → ℝ) (Af : ℂ → Set ℂ)
      (Dm : (β : ℂ) → β ∈ Λ → HeadDatum d Y κ ζa ζb β s) (ρp δp : ℝ) (Kp : Set ℂ),
      (∀ β ∈ Λ, 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b) →
      (∀ β ∈ Λ, (s = 1 ∧ AvailableUp d hd β ∧ κ ≤ β.im) ∨
        (s = -1 ∧ AvailableDown d hd β ∧ κ ≤ cl.im - β.im)) →
      (s = 1 ∨ s = -1) →
      (∀ β (h : β ∈ Λ), εf β = (Dm β h).ε) →
      (∀ β (h : β ∈ Λ), ρf β = min (Dm β h).ρ₁ ((Dm β h).C * min 1 C₂ / 4)) →
      (∀ β (h : β ∈ Λ), δf β = min (Dm β h).δ ((Dm β h).C')⁻¹) →
      (∀ β (h : β ∈ Λ), Af β = (Dm β h).A) →
      (∀ β' ∈ Λ, ∃ β ∈ Λ, ‖β' - β‖ < εf β ∧ ρp ≤ ρf β ∧ δp ≤ δf β ∧ Af β ⊆ Kp) →
      (δp = δ₀u ∨ δp = δ₀d) → ρ ≤ ρp → δ ≤ δp → Kp ⊆ K₁ ∪ K₂ → Kp ⊆ DR →
      (∀ w ∈ Kp, ‖R w - d.E w‖ < δ) →
      ∀ β ∈ Λ, ∃ W : ℕ → Set ℂ,
        (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
        (∀ j, IsOpen (W j) ∧ IsConnected (W j)) ∧
        (∀ j, W (j + 1) ⊆ DR ∧ Set.InjOn (fun w => R w - β) (W (j + 1)) ∧
          (fun w => R w - β) '' W (j + 1) = W j) ∧
        (∀ i j, i ≠ j → Disjoint (MandelDim.piExp '' W i) (MandelDim.piExp '' W j)) ∧
        (∀ M : ℝ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ w ∈ W j, M < s * w.im) ∧
        (∀ j, Bornology.IsBounded (W j) ∧ Metric.diam (W j) < 1 / 2) ∧
        (∀ j, ∃ u ∈ W j, ∃ u' ∈ W (j + 1), ‖u - u'‖ < C₀) ∧
        (∀ j, ∀ w ∈ W j, C₁ < ‖deriv ((fun u => R u - β)^[j]) w‖ ∧
          ‖deriv ((fun u => R u - β)^[j]) w‖ < C₁') := by
    intro s Λ εf ρf δf Af Dm ρp δp Kp hΛbox hΛhav hs hεeq hρeq hδeq hAeq hcov hδple hρρp
      hδδp hKpK hKpDR hKpclose β hβΛ
    obtain ⟨βi, hβiΛ, hdist, hρlo, hδlo, hAiK⟩ := hcov β hβΛ
    let D : HeadDatum d Y κ ζa ζb βi s := Dm βi hβiΛ
    have hDε : εf βi = D.ε := hεeq βi hβiΛ
    have hDρ : ρf βi = min D.ρ₁ (D.C * min 1 C₂ / 4) := hρeq βi hβiΛ
    have hDδ : δf βi = min D.δ (D.C')⁻¹ := hδeq βi hβiΛ
    have hDA : Af βi = D.A := hAeq βi hβiΛ
    have hβidist : ‖β - βi‖ < D.ε := by rw [← hDε]; exact hdist
    have hδppos : 0 < δp := lt_of_lt_of_le hδpos hδδp
    have hρmin : ρ ≤ min D.ρ₁ (D.C * min 1 C₂ / 4) := by
      rw [← hDρ]; exact le_trans hρρp hρlo
    have hρD : ρ ≤ D.ρ₁ := le_trans hρmin (min_le_left _ _)
    have hρDC : ρ ≤ D.C * min 1 C₂ / 4 := le_trans hρmin (min_le_right _ _)
    have hρ48 : ρ ≤ 1 / 48 := le_trans hρD (le_of_lt D.hρ48)
    have hδD : δ ≤ D.δ := by
      have h1 : δp ≤ min D.δ (D.C')⁻¹ := by rw [← hDδ]; exact hδlo
      exact le_trans hδδp (le_trans h1 (min_le_left _ _))
    have hδDinv : D.C' ≤ 1 / δp := by
      have h1 : δp ≤ (D.C')⁻¹ := by
        have h2 : δp ≤ min D.δ (D.C')⁻¹ := by rw [← hDδ]; exact hδlo
        exact le_trans h2 (min_le_right _ _)
      have h3 : δp * D.C' ≤ 1 := by
        have h4 : δp * D.C' ≤ (D.C')⁻¹ * D.C' :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt D.hC')
        rw [inv_mul_cancel₀ (ne_of_gt D.hC')] at h4
        exact h4
      rw [le_div_iff₀ hδppos]
      linarith
    have hDAK : D.A ⊆ Kp := by
      intro w hw
      rw [← hDA] at hw
      exact hAiK hw
    have hADR : D.A ⊆ DR := fun w hw => hKpDR (hDAK hw)
    have hcloseA : ∀ w ∈ D.A, ‖R w - d.E w‖ < D.δ := by
      intro w hw
      exact lt_of_lt_of_le (hKpclose w (hDAK hw)) hδD
    obtain ⟨W, hW0, hWoc, hWstep, hWdisj, hWdeep, hWlow, hWdiam24, hWdiamκ⟩ :=
      D.hmain ρ hρ hρD β hβidist R DR hDRo hADR hRdiff hcloseA
    have hWbdd : ∀ j, j ≤ D.j₀ → Bornology.IsBounded (W j) := fun j hj => (hWoc j hj).2.2.1
    have hWoc' : ∀ j, j ≤ D.j₀ → IsOpen (W j) ∧ IsConnected (W j) :=
      fun j hj => ⟨(hWoc j hj).1, (hWoc j hj).2.1⟩
    have hWd : ∀ j, j ≤ D.j₀ → Metric.diam (W j) < 1 / 2 := fun j hj => (hWoc j hj).2.2.2
    -- the numerical bounds on `C₁`, `C₁'`
    have hmC1 : min (1:ℝ) C₂ ≤ 1 := min_le_left _ _
    have hmC2 : min (1:ℝ) C₂ ≤ C₂ := min_le_right _ _
    have hmCpos : 0 < min (1:ℝ) C₂ := hminC
    have hρ_le : ρ ≤ D.C * min 1 C₂ / 4 := hρDC
    have hC₁_le_ρ : C₁ ≤ ρ := by
      rw [hC₁def]
      refine le_trans (min_le_right _ _) ?_
      have hmle1 : min (1:ℝ) C₂ ≤ 1 := min_le_left _ _
      nlinarith [hmle1, hρ]
    have hC₁_lt_C : C₁ < D.C := by
      have h : ρ ≤ D.C / 4 := by nlinarith [hρ_le, hmC1, D.hC]
      nlinarith [hC₁_le_ρ, h, D.hC]
    have hC₁_lt_CC : C₁ < D.C * C₂ := by
      have hmle : min (1:ℝ) C₂ ≤ C₂ := min_le_right _ _
      have hmle1 : min (1:ℝ) C₂ ≤ 1 := min_le_left _ _
      have h1 : C₁ ≤ ρ * min (1:ℝ) C₂ := by rw [hC₁def]; exact min_le_right _ _
      have h2 : ρ * min (1:ℝ) C₂ ≤ (D.C * min (1:ℝ) C₂ / 4) * min (1:ℝ) C₂ :=
        mul_le_mul_of_nonneg_right hρ_le (le_of_lt hmCpos)
      have h4 : (min (1:ℝ) C₂) * min (1:ℝ) C₂ ≤ C₂ := by nlinarith [hmle, hmle1, hmCpos]
      have h3 : (D.C * min (1:ℝ) C₂ / 4) * min (1:ℝ) C₂ ≤ D.C * C₂ / 4 := by
        nlinarith [h4, D.hC]
      have h5 : D.C * C₂ / 4 < D.C * C₂ := by nlinarith [D.hC, hC₂]
      linarith
    have hδp_le : (1 : ℝ) / δp ≤ max (δ₀u⁻¹ * max C₂' 1) (δ₀d⁻¹ * max C₂' 1) := by
      have hmax1 : (1:ℝ) ≤ max C₂' 1 := le_max_right _ _
      rcases hδple with h | h
      · have h1 : 0 < δ₀u := by rw [← h]; exact hδppos
        rw [h, one_div]
        exact le_trans (le_mul_of_one_le_right (le_of_lt (inv_pos.mpr h1)) hmax1)
          (le_max_left _ _)
      · have h1 : 0 < δ₀d := by rw [← h]; exact hδppos
        rw [h, one_div]
        exact le_trans (le_mul_of_one_le_right (le_of_lt (inv_pos.mpr h1)) hmax1)
          (le_max_right _ _)
    have hC'le : D.C' ≤ C₁' := by
      rw [hC₁'def]
      exact le_trans hδDinv (le_trans hδp_le (le_max_right _ _))
    have hC'le2 : D.C' * C₂' ≤ C₁' := by
      have h1 : D.C' * C₂' ≤ (1 / δp) * C₂' :=
        mul_le_mul_of_nonneg_right hδDinv (le_of_lt hC₂')
      have h2 : (1 / δp) * C₂' ≤ max (δ₀u⁻¹ * max C₂' 1) (δ₀d⁻¹ * max C₂' 1) := by
        have hmax : C₂' ≤ max C₂' 1 := le_max_left _ _
        rcases hδple with h | h
        · have h3 : 0 ≤ δ₀u⁻¹ := le_of_lt (inv_pos.mpr (by rw [← h]; exact hδppos))
          rw [h, one_div]
          exact le_trans (mul_le_mul_of_nonneg_left hmax h3) (le_max_left _ _)
        · have h3 : 0 ≤ δ₀d⁻¹ := le_of_lt (inv_pos.mpr (by rw [← h]; exact hδppos))
          rw [h, one_div]
          exact le_trans (mul_le_mul_of_nonneg_left hmax h3) (le_max_right _ _)
      rw [hC₁'def]
      exact le_trans (le_trans h1 h2) (le_max_right _ _)
    -- the tail from the head's last disc
    obtain ⟨V, hV0, hV⟩ := htailβ β (hΛbox β hβΛ).1 (hΛbox β hβΛ).2.1 (hΛbox β hβΛ).2.2
      s (hΛhav β hβΛ) R DR hDRo hTeq hRdiff hDRsubY hcloseY (W D.j₀)
      (hWoc D.j₀ le_rfl).1 (hWoc D.j₀ le_rfl).2.1 (hWoc D.j₀ le_rfl).2.2.1 hWdiam24 hWdiamκ hWdeep
    have hVht : ∀ t : ℕ, ∀ u ∈ V t, Y + (t : ℝ) * κ / 8 < s * u.im :=
      fun t => (hV t).2.2.2.2.2.1
    have hVder : ∀ t : ℕ, ∀ u ∈ V t, C₂ < ‖deriv ((fun u => R u - β)^[t]) u‖ ∧
        ‖deriv ((fun u => R u - β)^[t]) u‖ < C₂' := fun t => (hV t).2.2.2.2.2.2.2.2.2.2
    have hVdisj : ∀ i j : ℕ, i ≠ j →
        Disjoint (MandelDim.piExp '' V i) (MandelDim.piExp '' V j) :=
      fun i j hij => (hV 0).2.2.2.2.2.2.2.2.2.1 i j hij
    have hVec : ∀ t : ℕ, IsOpen (V t) ∧ IsConnected (V t) ∧ V (t + 1) ⊆ DR ∧
        Set.InjOn (fun u => R u - β) (V (t + 1)) ∧ (fun u => R u - β) '' V (t + 1) = V t ∧
        Bornology.IsBounded (V t) ∧ Metric.diam (V t) < 1 / 2 :=
      fun t => ⟨(hV t).1, (hV t).2.1, (hV t).2.2.1, (hV t).2.2.2.1, (hV t).2.2.2.2.1,
        (hV t).2.2.2.2.2.2.1, (hV t).2.2.2.2.2.2.2.1⟩
    have hVc0 : ∀ t : ℕ, ∃ u ∈ V t, ∃ u' ∈ V (t + 1), ‖u - u'‖ < C₀t :=
      fun t => (hV t).2.2.2.2.2.2.2.2.1
    -- the spliced chain
    let f : ℂ → ℂ := fun u => R u - β
    let W' : ℕ → Set ℂ := fun n => if n ≤ D.j₀ then W n else V (n - D.j₀)
    have hW'0 : W' 0 = W 0 := by
      show (if (0:ℕ) ≤ D.j₀ then W 0 else V (0 - D.j₀)) = W 0
      rw [if_pos (Nat.zero_le _)]
    have hW'low : ∀ n, n ≤ D.j₀ → W' n = W n := by
      intro n hn
      show (if n ≤ D.j₀ then W n else V (n - D.j₀)) = W n
      rw [if_pos hn]
    have hW'high : ∀ n, D.j₀ ≤ n → W' n = V (n - D.j₀) := by
      intro n hn
      rcases eq_or_lt_of_le hn with h | h
      · rw [← h, hW'low D.j₀ le_rfl, Nat.sub_self]
        exact hV0.symm
      · show (if n ≤ D.j₀ then W n else V (n - D.j₀)) = V (n - D.j₀)
        rw [if_neg (by omega)]
    have hW'step : ∀ n : ℕ, W' (n + 1) ⊆ DR ∧ Set.InjOn f (W' (n + 1)) ∧
        f '' W' (n + 1) = W' n := by
      intro n
      rcases lt_or_ge (n + 1) (D.j₀ + 1) with h | h
      · have hn : n + 1 ≤ D.j₀ := by omega
        have hnlt : n < D.j₀ := by omega
        obtain ⟨h1, h2, h3, -⟩ := hWstep n hnlt
        rw [hW'low (n + 1) hn, hW'low n (by omega)]
        exact ⟨fun w hw => hKpDR (hDAK (h1 hw)), h2, h3⟩
      · have hnj : D.j₀ ≤ n := by omega
        rw [hW'high (n + 1) (by omega), hW'high n hnj,
          show n + 1 - D.j₀ = (n - D.j₀) + 1 from by omega]
        exact ⟨(hV (n - D.j₀)).2.2.1, (hV (n - D.j₀)).2.2.2.1, (hV (n - D.j₀)).2.2.2.2.1⟩
    have hW'DR : ∀ n, 1 ≤ n → W' n ⊆ DR := by
      intro n hn
      rw [show n = (n - 1) + 1 from by omega]
      exact (hW'step (n - 1)).1
    have hiter : ∀ (i n : ℕ), i ≤ n → ∀ w ∈ W' n, (f^[i]) w ∈ W' (n - i) := by
      intro i
      induction i with
      | zero => intro n _ w hw; simpa using hw
      | succ k ih =>
        intro n hk w hw
        have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
        have hkn : k < n := hk
        have hmem : (f^[k]) w ∈ W' (n - k) := ih n hk' w hw
        have hk1 : n - (k + 1) = n - k - 1 := by omega
        have hk2 : n - k = (n - k - 1) + 1 := by omega
        have himg : (f^[k + 1]) w = f ((f^[k]) w) := Function.iterate_succ_apply' f k w
        have hstep : f '' W' (n - k) = W' (n - k - 1) := by
          rw [hk2]; exact (hW'step (n - k - 1)).2.2
        rw [himg, hk1, ← hstep]
        exact Set.mem_image_of_mem f hmem
    have hfAt : ∀ y ∈ DR, DifferentiableAt ℂ f y := by
      intro y hy
      show DifferentiableAt ℂ (fun u => R u - β) y
      exact (hRdiff.differentiableAt (hDRo.mem_nhds hy)).sub_const β
    have hdiff : ∀ (i n : ℕ), i ≤ n → ∀ w ∈ W' n, DifferentiableAt ℂ (f^[i]) w := by
      intro i
      induction i with
      | zero => intro n _ w _; simpa using differentiableAt_id
      | succ k ih =>
        intro n hk w hw
        have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
        have hmem : (f^[k]) w ∈ W' (n - k) := hiter k n hk' w hw
        have hmemDR : (f^[k]) w ∈ DR := hW'DR (n - k) (by omega) hmem
        rw [show f^[k + 1] = f ∘ f^[k] from
          funext (fun x => Function.iterate_succ_apply' f k x)]
        exact (hfAt _ hmemDR).comp w (ih n hk' w hw)
    -- the escape along the spliced chain
    have hWesc : ∀ M : ℝ, ∃ J : ℕ, ∀ n, J ≤ n → ∀ w ∈ W' n, M < s * w.im := by
      intro M
      obtain ⟨T, hT⟩ : ∃ T : ℕ, M < Y + (T : ℝ) * (κ / 8) := by
        obtain ⟨T, hT⟩ := exists_nat_gt ((M - Y) * (8 / κ))
        refine ⟨T, ?_⟩
        have h2 : (0:ℝ) < κ / 8 := by positivity
        have h4 : ((8:ℝ) / κ) * (κ / 8) = 1 := by field_simp
        have h5 : ((M - Y) * (8 / κ)) * (κ / 8) = M - Y := by rw [mul_assoc, h4, mul_one]
        have h3 := mul_lt_mul_of_pos_right hT h2
        rw [h5] at h3
        linarith
      refine ⟨D.j₀ + T, fun n hn w hw => ?_⟩
      have hjn : D.j₀ ≤ n := by omega
      have htn : T ≤ n - D.j₀ := by omega
      rw [hW'high n hjn] at hw
      have h6 : ((T : ℕ) : ℝ) * (κ / 8) ≤ (((n - D.j₀ : ℕ) : ℝ)) * (κ / 8) := by
        have h3 : ((T : ℕ) : ℝ) ≤ (((n - D.j₀ : ℕ)) : ℝ) := by exact_mod_cast htn
        exact mul_le_mul_of_nonneg_right h3 (by positivity)
      have h7 : M < Y + (((n - D.j₀ : ℕ)) : ℝ) * (κ / 8) := by linarith
      have h8 := hVht (n - D.j₀) w hw
      linarith
    have hC₀_t : C₀t ≤ C₀ := by rw [hC₀def]; exact le_max_left _ _
    have hC₀_d : Metric.diam (K₁ ∪ K₂) < C₀ := by
      rw [hC₀def]
      refine lt_of_lt_of_le (by linarith : Metric.diam (K₁ ∪ K₂) < Metric.diam (K₁ ∪ K₂) + 1) ?_
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hC₀_n : MK + max ‖ζa‖ ‖ζb‖ + 1 < C₀ := by
      rw [hC₀def]
      refine lt_of_lt_of_le (by linarith : MK + max ‖ζa‖ ‖ζb‖ + 1 < MK + max ‖ζa‖ ‖ζb‖ + 2) ?_
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨W', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hW'0]
      rcases D.hζ with h | h
      · exact Or.inl (by rw [hW0, h])
      · exact Or.inr (by rw [hW0, h])
    · intro n
      by_cases hn : n ≤ D.j₀
      · rw [hW'low n hn]; exact hWoc' n hn
      · rw [hW'high n (by omega)]
        exact ⟨(hV (n - D.j₀)).1, (hV (n - D.j₀)).2.1⟩
    · exact hW'step
    · intro i j hij
      refine Set.disjoint_left.mpr ?_
      rintro a ⟨u, hu, rfl⟩ ⟨v, hv, hveq⟩
      have him : v.im = u.im := piExp_im_ne hveq
      have hsne : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
      by_cases hi : i ≤ D.j₀
      · by_cases hj : j ≤ D.j₀
        · rw [hW'low i hi] at hu
          rw [hW'low j hj] at hv
          exact (Set.disjoint_left.mp (hWdisj i j hi hj hij) ⟨u, hu, rfl⟩) ⟨v, hv, hveq⟩
        · by_cases hip : i = D.j₀
          · have h0 : W' D.j₀ = V 0 := by
              rw [hW'low D.j₀ le_rfl]; exact hV0.symm
            rw [hip] at hu
            rw [h0] at hu
            rw [hW'high j (by omega)] at hv
            have hne : (0:ℕ) ≠ j - D.j₀ := by omega
            exact (Set.disjoint_left.mp (hVdisj 0 (j - D.j₀) hne) ⟨u, hu, rfl⟩) ⟨v, hv, hveq⟩
          · have hi' : i < D.j₀ := lt_of_le_of_ne hi hip
            rw [hW'low i hi] at hu
            rw [hW'high j (by omega)] at hv
            have h1 : s * u.im < Y + κ / 8 := hWlow i hi' u hu
            have h2 : Y + κ / 8 < s * v.im := by
              have h3 := hVht (j - D.j₀) v hv
              have h4 : (1:ℝ) ≤ ((j - D.j₀ : ℕ) : ℝ) := by
                have : 1 ≤ j - D.j₀ := by omega
                exact_mod_cast this
              nlinarith [h4, hκpos, h3]
            rw [him] at h2
            linarith
      · by_cases hj : j ≤ D.j₀
        · by_cases hjp : j = D.j₀
          · have h0 : W' D.j₀ = V 0 := by
              rw [hW'low D.j₀ le_rfl]; exact hV0.symm
            rw [hjp] at hv
            rw [h0] at hv
            rw [hW'high i (by omega)] at hu
            have hne : i - D.j₀ ≠ 0 := by omega
            exact (Set.disjoint_left.mp (hVdisj (i - D.j₀) 0 hne) ⟨u, hu, rfl⟩) ⟨v, hv, hveq⟩
          · have hj' : j < D.j₀ := lt_of_le_of_ne hj hjp
            rw [hW'high i (by omega)] at hu
            rw [hW'low j hj] at hv
            have h1 : s * v.im < Y + κ / 8 := hWlow j hj' v hv
            have h2 : Y + κ / 8 < s * u.im := by
              have h3 := hVht (i - D.j₀) u hu
              have h4 : (1:ℝ) ≤ ((i - D.j₀ : ℕ) : ℝ) := by
                have : 1 ≤ i - D.j₀ := by omega
                exact_mod_cast this
              nlinarith [h4, hκpos, h3]
            rw [him] at h1
            linarith
        · rw [hW'high i (by omega)] at hu
          rw [hW'high j (by omega)] at hv
          have hne : i - D.j₀ ≠ j - D.j₀ := by omega
          exact (Set.disjoint_left.mp (hVdisj (i - D.j₀) (j - D.j₀) hne) ⟨u, hu, rfl⟩)
            ⟨v, hv, hveq⟩
    · exact hWesc
    · intro n
      by_cases hn : n ≤ D.j₀
      · rw [hW'low n hn]; exact ⟨hWbdd n hn, hWd n hn⟩
      · rw [hW'high n (by omega)]
        exact ⟨(hV (n - D.j₀)).2.2.2.2.2.2.1, (hV (n - D.j₀)).2.2.2.2.2.2.2.1⟩
    · intro n
      by_cases hn : n + 1 ≤ D.j₀
      · have hn' : n ≤ D.j₀ := by omega
        have hmn : n < D.j₀ := by omega
        rw [hW'low n hn', hW'low (n + 1) hn]
        obtain ⟨u, hu⟩ := (hWoc' n hn').2.nonempty
        obtain ⟨u', hu'⟩ := (hWoc' (n + 1) hn).2.nonempty
        refine ⟨u, hu, u', hu', ?_⟩
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have huball : u ∈ Metric.ball D.ζ ρ := by rw [← hW0]; exact hu
          have h1 : ‖u'‖ ≤ MK := by
            have h2 := hMK u' (hKpK (hDAK ((hWstep 0 hmn).1 hu')))
            simpa using h2
          have h2 : ‖u‖ ≤ ‖D.ζ‖ + ρ := by
            have h3 : ‖u - D.ζ‖ < ρ := by
              have hh := Metric.mem_ball.mp huball
              rwa [dist_eq_norm] at hh
            have h5 : ‖u‖ ≤ ‖u - D.ζ‖ + ‖D.ζ‖ := by
              calc ‖u‖ = ‖(u - D.ζ) + D.ζ‖ := by ring_nf
                _ ≤ ‖u - D.ζ‖ + ‖D.ζ‖ := norm_add_le _ _
            linarith
          have h3 : ‖D.ζ‖ ≤ max ‖ζa‖ ‖ζb‖ := by
            rcases D.hζ with h | h
            · rw [h]; exact le_max_left _ _
            · rw [h]; exact le_max_right _ _
          have h4 : ‖u - u'‖ ≤ MK + max ‖ζa‖ ‖ζb‖ + 1 := by
            have h5 : ‖u - u'‖ ≤ ‖u‖ + ‖u'‖ := norm_sub_le _ _
            linarith
          exact lt_of_le_of_lt h4 hC₀_n
        · have huK : u ∈ K₁ ∪ K₂ := by
            have h2 := (hWstep (n - 1) (by omega)).1
            rw [Nat.sub_add_cancel hpos] at h2
            exact hKpK (hDAK (h2 hu))
          have hu'K : u' ∈ K₁ ∪ K₂ := by
            exact hKpK (hDAK ((hWstep n hmn).1 hu'))
          exact lt_of_le_of_lt (by simpa [dist_eq_norm] using
            Metric.dist_le_diam_of_mem hKbdd huK hu'K) hC₀_d
      · rw [hW'high n (by omega), hW'high (n + 1) (by omega),
          show n + 1 - D.j₀ = (n - D.j₀) + 1 from by omega]
        obtain ⟨u, hu, u', hu', hd⟩ := hVc0 (n - D.j₀)
        exact ⟨u, hu, u', hu', lt_of_lt_of_le hd hC₀_t⟩
    · intro n w hw
      have hw' : w ∈ W' n := hw
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        rw [hW'low 0 (Nat.zero_le _), hW0] at hw
        have h1 : deriv ((fun u => R u - β)^[0]) w = 1 := by simp
        rw [h1]
        refine ⟨?_, ?_⟩
        · rw [hC₁def]
          exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
        · rw [hC₁'def]
          exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      · have hf0 : ∀ u : ℂ, (fun u => R u - β)^[0] u = u := fun u => rfl
        by_cases hnJ : n ≤ D.j₀
        · rw [hW'low n hnJ] at hw
          obtain ⟨-, -, -, hder⟩ := hWstep (n - 1) (by omega)
          have hmem : w ∈ W ((n - 1) + 1) := by rwa [Nat.sub_add_cancel hnpos]
          have hb := hder w hmem
          rw [Nat.sub_add_cancel hnpos] at hb
          exact ⟨lt_trans hC₁_lt_C hb.1, lt_of_lt_of_le hb.2 hC'le⟩
        · have hjn : D.j₀ ≤ n := by omega
          rw [hW'high n hjn] at hw
          have htle : n - D.j₀ ≤ n := Nat.sub_le _ _
          have hmemt : (f^[n - D.j₀]) w ∈ W' D.j₀ := by
            have h := hiter (n - D.j₀) n htle w hw'
            rwa [show n - (n - D.j₀) = D.j₀ from by omega] at h
          have hmemV : (f^[n - D.j₀]) w ∈ V 0 := by
            rw [hW'high D.j₀ le_rfl, Nat.sub_self] at hmemt
            exact hmemt
          have hmemW : (f^[n - D.j₀]) w ∈ W D.j₀ := by rw [← hV0]; exact hmemV
          have hD1 : DifferentiableAt ℂ (f^[D.j₀]) ((f^[n - D.j₀]) w) :=
            hdiff D.j₀ D.j₀ le_rfl _ hmemt
          have hD2 : DifferentiableAt ℂ (f^[n - D.j₀]) w := hdiff (n - D.j₀) n htle w hw'
          have hdecomp : deriv (f^[n]) w =
              deriv (f^[D.j₀]) ((f^[n - D.j₀]) w) * deriv (f^[n - D.j₀]) w := by
            have h := deriv_iterate_add (m := D.j₀) (n := n - D.j₀) hD1 hD2
            rwa [Nat.add_sub_cancel' hjn] at h
          have hH : D.C < ‖deriv (f^[D.j₀]) ((f^[n - D.j₀]) w)‖ ∧
              ‖deriv (f^[D.j₀]) ((f^[n - D.j₀]) w)‖ < D.C' := by
            have h := (hWstep (D.j₀ - 1) (Nat.sub_one_lt (ne_of_gt D.hj₀))).2.2.2
            rw [Nat.sub_add_cancel D.hj₀] at h
            exact h _ hmemW
          have hT := hVder (n - D.j₀) w hw
          rw [hdecomp, norm_mul]
          refine ⟨?_, ?_⟩
          · have h1 : D.C * C₂ ≤ ‖deriv (f^[D.j₀]) ((f^[n - D.j₀]) w)‖ *
                ‖deriv (f^[n - D.j₀]) w‖ :=
              mul_le_mul hH.1.le hT.1.le (le_of_lt hC₂) (norm_nonneg _)
            exact lt_of_lt_of_le hC₁_lt_CC h1
          · have h1 : ‖deriv (f^[D.j₀]) ((f^[n - D.j₀]) w)‖ * ‖deriv (f^[n - D.j₀]) w‖ <
                D.C' * C₂' := by
              have h2 : 0 < ‖deriv (f^[n - D.j₀]) w‖ := lt_trans hC₂ hT.1
              calc ‖deriv (f^[D.j₀]) ((f^[n - D.j₀]) w)‖ * ‖deriv (f^[n - D.j₀]) w‖
                  < D.C' * ‖deriv (f^[n - D.j₀]) w‖ :=
                    mul_lt_mul_of_pos_right hH.2 h2
                _ ≤ D.C' * C₂' := mul_le_mul_of_nonneg_left hT.2.le (le_of_lt D.hC')
            exact lt_of_lt_of_le h1 hC'le2
  -- ## the two cases
  intro β hβ0 hβ1 hβb
  have hεeqU : ∀ β (h : β ∈ upBox d hd b κ), upε β = (upD β h).ε := by
    intro β hβ; simp only [upε, dif_pos hβ]
  have hρeqU : ∀ β (h : β ∈ upBox d hd b κ),
      upρ β = min (upD β h).ρ₁ ((upD β h).C * min 1 C₂ / 4) := by
    intro β hβ; simp only [upρ, dif_pos hβ]
  have hδeqU : ∀ β (h : β ∈ upBox d hd b κ), upδ β = min (upD β h).δ ((upD β h).C')⁻¹ := by
    intro β hβ; simp only [upδ, dif_pos hβ]
  have hAeqU : ∀ β (h : β ∈ upBox d hd b κ), upA β = (upD β h).A := by
    intro β hβ; simp only [upA, dif_pos hβ]
  have hεeqD : ∀ β (h : β ∈ dnBox d hd b κ cl), dnε β = (dnD β h).ε := by
    intro β hβ; simp only [dnε, dif_pos hβ]
  have hρeqD : ∀ β (h : β ∈ dnBox d hd b κ cl),
      dnρ β = min (dnD β h).ρ₁ ((dnD β h).C * min 1 C₂ / 4) := by
    intro β hβ; simp only [dnρ, dif_pos hβ]
  have hδeqD : ∀ β (h : β ∈ dnBox d hd b κ cl), dnδ β = min (dnD β h).δ ((dnD β h).C')⁻¹ := by
    intro β hβ; simp only [dnδ, dif_pos hβ]
  have hAeqD : ∀ β (h : β ∈ dnBox d hd b κ cl), dnA β = (dnD β h).A := by
    intro β hβ; simp only [dnA, dif_pos hβ]
  have hcov₁' : ∀ β' ∈ upBox d hd b κ, ∃ β ∈ upBox d hd b κ, ‖β' - β‖ < upε β ∧
      ρ₀u ≤ upρ β ∧ δ₀u ≤ upδ β ∧ upA β ⊆ K₁ := by
    intro β' hβ'
    obtain ⟨β, hβt, h1, h2, h3⟩ := hcov₁ β' hβ'
    exact ⟨β, ht₁ β hβt, h1, h2, h3, hA₁K β hβt⟩
  have hcov₂' : ∀ β' ∈ dnBox d hd b κ cl, ∃ β ∈ dnBox d hd b κ cl, ‖β' - β‖ < dnε β ∧
      ρ₀d ≤ dnρ β ∧ δ₀d ≤ dnδ β ∧ dnA β ⊆ K₂ := by
    intro β' hβ'
    obtain ⟨β, hβt, h1, h2, h3⟩ := hcov₂ β' hβ'
    exact ⟨β, ht₂ β hβt, h1, h2, h3, hA₂K β hβt⟩
  rcases hunif β with ⟨havU, hκβ⟩ | ⟨havD, hκcl⟩
  · have hβup : β ∈ upBox d hd b κ := ⟨hβ0, hβ1, hβb, havU, hκβ⟩
    obtain ⟨W, h1, h2, h3, h4, h5, h6, h7, h8⟩ := step 1 (upBox d hd b κ) upε upρ upδ upA upD
      ρ₀u δ₀u K₁ (fun β hβ => ⟨hβ.1, hβ.2.1, hβ.2.2.1⟩)
      (fun β hβ => Or.inl ⟨rfl, hβ.2.2.2.1, hβ.2.2.2.2⟩) (Or.inl rfl) hεeqU hρeqU hδeqU hAeqU
      hcov₁' (Or.inl rfl) hρu hδδu (fun w hw => Or.inl hw)
      (fun w hw => hDRsub (Or.inl (Or.inl hw)))
      (fun w hw => hclose w (Or.inl (Or.inl hw))) β hβup
    exact ⟨W, 1, Or.inl rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · have hβdn : β ∈ dnBox d hd b κ cl := ⟨hβ0, hβ1, hβb, havD, hκcl⟩
    obtain ⟨W, h1, h2, h3, h4, h5, h6, h7, h8⟩ := step (-1) (dnBox d hd b κ cl) dnε dnρ dnδ dnA
      dnD ρ₀d δ₀d K₂ (fun β hβ => ⟨hβ.1, hβ.2.1, hβ.2.2.1⟩)
      (fun β hβ => Or.inr ⟨rfl, hβ.2.2.2.1, hβ.2.2.2.2⟩) (Or.inr rfl) hεeqD hρeqD hδeqD hAeqD
      hcov₂' (Or.inr rfl) hρd hδδd (fun w hw => Or.inr hw)
      (fun w hw => hDRsub (Or.inl (Or.inr hw)))
      (fun w hw => hclose w (Or.inl (Or.inr hw))) β hβdn
    exact ⟨W, -1, Or.inr rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩

end

end Work.L62
