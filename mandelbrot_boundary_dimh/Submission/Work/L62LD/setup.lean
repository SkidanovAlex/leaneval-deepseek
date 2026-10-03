import Mathlib
import Submission.Work.L62.lowcyl
import Submission.Work.L62.l62c_end
import Submission.Work.L62.availableDown_box
import Submission.Work.L62LD.escape

/-!
# L62LD — the basic objects of the lower-end head of Lemma 6.2

This file fixes the vocabulary used by the proof of `Work.L62.model_head_down_deep`:

* `Work.L62LD.Chain d hd β W` — a *backward chain of discs* for `ĥ = d.E - β` (Shishikura,
  Lemma 6.2): the discs are open, connected, `ĥ` maps `W (j+1)` bijectively onto `W j`, and the
  discs of index `≥ 1` lie in the lower horn `hd.Bl`;
* `Chain.iterate_image` / `Chain.iterate_mem` — `ĥ^[m]` maps `W j` onto `W (j-m)`;
* `Work.L62LD.downBox` (the `β`-box of Lemma 6.2 intersected with `AvailableDown`, compact by
  `Work.L62LD.isCompact_downBox`), the *good-centre* sets
  `Work.L62LD.good ζ₀ v τ = {β | ∀ k : ℤ, τ ≤ ‖ζ₀ + β - (v + k)‖}` (closed), and the covering
  `downBox ⊆ good ζa v τ ∪ good ζb v τ` obtained from `Work.L62.exists_avoiding_center`.
* `Work.L62LD.exists_drift` — the uniform drift `κ > 0` on the box.
-/

namespace Work.L62LD

open Classical MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Chains of discs -/

/-- A backward chain of discs for `ĥ = d.E - β`: `W j` is open and connected, `ĥ` maps
`W (j+1)` bijectively onto `W j`, and every disc of positive index lies in the lower horn. -/
structure Chain (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (β : ℂ)
    (W : ℕ → Set ℂ) : Prop where
  opconn : ∀ j : ℕ, IsOpen (W j) ∧ IsConnected (W j)
  inj : ∀ j : ℕ, Set.InjOn (fun w => d.E w - β) (W (j + 1))
  img : ∀ j : ℕ, (fun w => d.E w - β) '' W (j + 1) = W j
  mem_Bl : ∀ j : ℕ, 1 ≤ j → W j ⊆ hd.Bl

theorem Chain.iterate_image {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d}
    {β : ℂ} {W : ℕ → Set ℂ} (hc : Chain d hd β W) :
    ∀ j m : ℕ, m ≤ j → ((fun w => d.E w - β)^[m]) '' W j = W (j - m) := by
  intro j m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
      intro hm
      have hkj : k ≤ j := le_trans (Nat.le_succ k) hm
      have hcomp : ((fun w => d.E w - β)^[k + 1]) '' W j
          = (fun w => d.E w - β) '' (((fun w => d.E w - β)^[k]) '' W j) := by
        rw [Function.iterate_succ', Set.image_comp]
      rw [hcomp, ih hkj]
      have h1k : 1 ≤ j - k := by omega
      have hjk : j - k = (j - k - 1) + 1 := by omega
      have harith : j - k - 1 = j - (k + 1) := by omega
      rw [hjk, hc.img (j - k - 1), harith]

theorem Chain.iterate_mem {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d}
    {β : ℂ} {W : ℕ → Set ℂ} (hc : Chain d hd β W) {j m : ℕ} (hm : m ≤ j) {w : ℂ}
    (hw : w ∈ W j) : ((fun w => d.E w - β)^[m]) w ∈ W (j - m) := by
  have h := hc.iterate_image j m hm
  rw [← h]
  exact ⟨w, hw, rfl⟩

/-! ## The good-centre sets -/

/-- `β` is a *good* parameter for the centre `ζ₀` if the `β`-translate of `ζ₀` keeps distance at
least `τ` from the critical class `v + ℤ`. -/
def good (ζ₀ v : ℂ) (τ : ℝ) : Set ℂ := {β : ℂ | ∀ k : ℤ, τ ≤ ‖ζ₀ + β - (v + (k : ℂ))‖}

theorem isClosed_good (ζ₀ v : ℂ) (τ : ℝ) : IsClosed (good ζ₀ v τ) := by
  rw [← isOpen_compl_iff]
  have hset : (good ζ₀ v τ)ᶜ = ⋃ k : ℤ, {β : ℂ | ‖ζ₀ + β - (v + (k : ℂ))‖ < τ} := by
    ext β
    simp only [good, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_forall, not_le]
  rw [hset]
  refine isOpen_iUnion fun k => isOpen_lt ?_ continuous_const
  exact continuous_norm.comp (by fun_prop)

theorem mem_good_iff {ζ₀ v : ℂ} {τ : ℝ} {β : ℂ} :
    β ∈ good ζ₀ v τ ↔ ∀ k : ℤ, τ ≤ ‖ζ₀ + β - (v + (k : ℂ))‖ := Iff.rfl

/-- **The two good-centre sets cover the box.**  `ζa ≢ ζb (mod ℤ)` with separation `δ`; for
`2τ < δ` every `β` of the box is good for at least one of the two centres. -/
theorem downBox_subset_good_union {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d}
    {ζa ζb : ℂ} {δ τ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ k : ℤ, δ ≤ ‖(ζa - ζb) - (k : ℂ)‖) (hτ : 2 * τ < δ) (b : ℝ) :
    downBox d hd b ⊆ good ζa hd.v τ ∪ good ζb hd.v τ := by
  intro β hβ
  obtain ⟨ζ, hζmem, hζdist⟩ :=
    Work.L62.exists_avoiding_center d hd (ρ := τ) (δ := δ) (β := β) hδ hsep hτ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζmem
  rcases hζmem with h | h
  · left
    subst h
    exact fun k => le_of_lt (hζdist k)
  · right
    subst h
    exact fun k => le_of_lt (hζdist k)

/-- A good set is open in the complement of nothing — but the box with one good condition is
compact. -/
theorem isCompact_downBox_inter_good {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d}
    {ζ₀ : ℂ} {τ b : ℝ} : IsCompact (downBox d hd b ∩ good ζ₀ hd.v τ) :=
  (isCompact_downBox d hd b).inter_right (isClosed_good ζ₀ hd.v τ)

/-- On a good set, the `havoid` hypothesis of `Work.L62HD.section_over_ball_in_compact` holds. -/
theorem good_havoid {ζ₀ v : ℂ} {τ ρ : ℝ} (h : 2 * ρ < τ) {β : ℂ} (hβ : β ∈ good ζ₀ v τ) :
    ∀ k : ℤ, 2 * ρ < ‖ζ₀ + β - (v + (k : ℂ))‖ :=
  fun k => lt_of_lt_of_le h (hβ k)

/-! ## The uniform drift on the box -/

/-- **The uniform drift of the lower end on the `β`-box.**  Since `β ↦ cl.im - β.im` is continuous
and strictly positive on the compact box (`Work.L62.avail_down`), it has a positive lower
bound. -/
theorem exists_drift {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl)) (b : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ β ∈ downBox d hd b, β.im ≤ cl.im - κ := by
  rcases Set.eq_empty_or_nonempty (downBox d hd b) with hemp | ⟨β₀, hβ₀⟩
  · exact ⟨1, one_pos, fun β hβ => absurd hβ (hemp ▸ Set.notMem_empty β)⟩
  · obtain ⟨β₁, hβ₁, hmin⟩ := (isCompact_downBox d hd b).exists_isMinOn ⟨β₀, hβ₀⟩
      (continuous_const.sub Complex.continuous_im).continuousOn
    refine ⟨cl.im - β₁.im, sub_pos.mpr (Work.L62.avail_down d hd hcl hβ₁.2), fun β hβ => ?_⟩
    have h1 : cl.im - β₁.im ≤ cl.im - β.im := (isMinOn_iff.mp hmin) β hβ
    linarith

end

end Work.L62LD
