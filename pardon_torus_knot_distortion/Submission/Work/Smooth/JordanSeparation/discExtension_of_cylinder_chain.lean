import Mathlib
import Submission.Work.Smooth.JordanSeparation.Transfer
import Submission.Work.Smooth.SphereJordan.OpenImageAux

/-!
# A chain of embedded cylinders shrinking to a point bounds an embedded disc

This file proves `Work.Smooth.JordanSeparation.discExtension_of_cylinder_chain`: given a
`2π`-periodic continuous curve `γ`, an infinite chain of embedded cylinders `Φ k : S¹ × [0,1] → ℂ`
glued consecutively (`Φ (k+1) (·,0) = Φ k (·,1)`) and pairwise disjoint except along the glued
boundary circles, shrinking uniformly to a point `p`, the curve `γ = Φ 0 (·,0)` is the boundary
circle of an injective map of the disc.

The disc filling is written down explicitly: the radial coordinate `r ∈ (0,1]` is sent to the
"level" `t = 1/r - 1` of the chain, and `w = r e^{iθ}` is sent to `Φ ⌊t⌋ (θ, t - ⌊t⌋)`; the
remaining point `0` is sent to the limit point `p`.  The two facts that make this injective are

* the glued chain map `(θ,t) ↦ Φ ⌊t⌋ (θ, t - ⌊t⌋)` is injective modulo `2π` in `θ`
  (`ChainData.Psi_inj`), and
* the point `p` is *not* attained by the chain at all (`ChainData.not_hit`).

The second is the delicate point, and is where Brouwer's invariance of domain
(`Work.Smooth.SphereJordan.mem_interior_image_of_norm_lt_one`) enters: if `p` were attained, the
"tail" of the chain from one cylinder further on would be an embedded disc whose boundary
accumulates at the attained point `p`, hence would fill a *neighbourhood* of `p`; but the tail
intersects the cylinder that attains `p` only along that cylinder's far boundary curve, giving a
contradiction.
-/

open Set
open Work.Smooth.Jordan
open scoped Topology

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The data and hypotheses of the cylinder-chain lemma: a `2π`-periodic curve `γ`, a chain of
injective cylinders `Φ k` glued consecutively (`Φ (k+1) (·,0) = Φ k (·,1)`), pairwise disjoint
except along the glued boundary circles, shrinking uniformly to a point `p`. -/
structure ChainData (γ : ℝ → ℂ) (Φ : ℕ → ℝ × ℝ → ℂ) (p : ℂ) : Prop where
  /-- the curve is continuous -/
  cont : Continuous γ
  /-- the curve is `2π`-periodic -/
  per : Function.Periodic γ (2 * Real.pi)
  /-- every cylinder is continuous -/
  hcont : ∀ k, Continuous (Φ k)
  /-- every cylinder is `2π`-periodic in the first variable -/
  hper : ∀ (k : ℕ) (θ s : ℝ), Φ k (θ + 2 * Real.pi, s) = Φ k (θ, s)
  /-- the zeroth cylinder starts at `γ` -/
  hzero : ∀ θ : ℝ, Φ 0 (θ, 0) = γ θ
  /-- consecutive cylinders are glued -/
  hmatch : ∀ (k : ℕ) (θ : ℝ), Φ (k + 1) (θ, 0) = Φ k (θ, 1)
  /-- each cylinder is injective modulo the period -/
  hinj : ∀ (k : ℕ) (θ s θ' s' : ℝ), s ∈ Set.Icc 0 1 → s' ∈ Set.Icc 0 1 →
      Φ k (θ, s) = Φ k (θ', s') → s = s' ∧ ∃ m : ℤ, θ' = θ + m * (2 * Real.pi)
  /-- distinct cylinders meet only along the glued boundary circles -/
  hdisj : ∀ (k k' : ℕ) (θ s θ' s' : ℝ), k < k' → s ∈ Set.Icc 0 1 → s' ∈ Set.Icc 0 1 →
      Φ k (θ, s) = Φ k' (θ', s') →
      s = 1 ∧ s' = 0 ∧ ∃ m : ℤ, θ' = θ + m * (2 * Real.pi)
  /-- the chain shrinks to `p` -/
  hshrink : ∀ ε > 0, ∃ K, ∀ k ≥ K, ∀ (θ s : ℝ), s ∈ Set.Icc 0 1 → ‖Φ k (θ, s) - p‖ < ε

/-! ## Elementary facts about the disc -/

theorem disc_norm_le_one (w : Disc) : ‖(w : ℂ)‖ ≤ 1 := by
  have h := w.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

noncomputable def chainLevel (K : ℕ) (w : Disc) : ℝ := (K : ℝ) + (1 / ‖(w : ℂ)‖ - 1)

theorem chainLevel_nonneg (K : ℕ) {w : Disc} (hw : (w : ℂ) ≠ 0) : 0 ≤ chainLevel K w := by
  have hpos : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr hw
  have h1 : 1 ≤ 1 / ‖(w : ℂ)‖ := by
    rw [one_le_div hpos]
    exact disc_norm_le_one w
  simp only [chainLevel]
  linarith

theorem le_floor_chainLevel (K : ℕ) {w : Disc} (hw : (w : ℂ) ≠ 0) :
    K ≤ Nat.floor (chainLevel K w) := by
  refine Nat.le_floor ?_
  have hpos : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr hw
  have h1 : 1 ≤ 1 / ‖(w : ℂ)‖ := by
    rw [one_le_div hpos]
    exact disc_norm_le_one w
  simp only [chainLevel]
  linarith

namespace ChainData

variable {γ : ℝ → ℂ} {Φ : ℕ → ℝ × ℝ → ℂ} {p : ℂ}

/-! ## The glued chain map -/

/-- The glued chain map: `(θ,t) ↦ Φ ⌊t⌋ (θ, t - ⌊t⌋)`. -/
def Psi (C : ChainData γ Φ p) (θ t : ℝ) : ℂ := Φ (Nat.floor t) (θ, t - (Nat.floor t : ℝ))

theorem Psi_frac_mem (C : ChainData γ Φ p) {t : ℝ} (ht : 0 ≤ t) :
    t - (Nat.floor t : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [Nat.floor_le ht], by linarith [Nat.lt_floor_add_one t]⟩

theorem Psi_natCast (C : ChainData γ Φ p) (k : ℕ) (θ : ℝ) : C.Psi θ (k : ℝ) = Φ k (θ, 0) := by
  simp [Psi]

theorem Psi_periodic (C : ChainData γ Φ p) (θ t : ℝ) :
    C.Psi (θ + 2 * Real.pi) t = C.Psi θ t := by
  simp only [Psi]
  exact C.hper (Nat.floor t) θ (t - (Nat.floor t : ℝ))

/-- The glued chain map is injective modulo the period, for `t, t' ≥ 0`. -/
theorem Psi_inj (C : ChainData γ Φ p) {θ t θ' t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (h : C.Psi θ t = C.Psi θ' t') : t = t' ∧ ∃ m : ℤ, θ' = θ + m * (2 * Real.pi) := by
  have hmain : Φ (Nat.floor t) (θ, t - (Nat.floor t : ℝ))
      = Φ (Nat.floor t') (θ', t' - (Nat.floor t' : ℝ)) := h
  have hs : t - (Nat.floor t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := C.Psi_frac_mem ht
  have hs' : t' - (Nat.floor t' : ℝ) ∈ Set.Icc (0 : ℝ) 1 := C.Psi_frac_mem ht'
  have hlt1 : t - (Nat.floor t : ℝ) < 1 := by linarith [Nat.lt_floor_add_one t]
  have hlt1' : t' - (Nat.floor t' : ℝ) < 1 := by linarith [Nat.lt_floor_add_one t']
  rcases lt_trichotomy (Nat.floor t) (Nat.floor t') with hlt | heq | hgt
  · have h1 := C.hdisj (k := Nat.floor t) (k' := Nat.floor t') (θ := θ)
      (s := t - (Nat.floor t : ℝ)) (θ' := θ') (s' := t' - (Nat.floor t' : ℝ)) hlt hs hs' hmain
    linarith [h1.1]
  · have hmain' : Φ (Nat.floor t) (θ, t - (Nat.floor t : ℝ))
        = Φ (Nat.floor t) (θ', t' - (Nat.floor t : ℝ)) := by
      simpa only [← heq] using hmain
    have hs'' : t' - (Nat.floor t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      have hcast' : ((Nat.floor t : ℕ) : ℝ) = ((Nat.floor t' : ℕ) : ℝ) := by exact_mod_cast heq
      rwa [← hcast'] at hs'
    have h2 := C.hinj (k := Nat.floor t) (θ := θ) (s := t - (Nat.floor t : ℝ))
      (θ' := θ') (s' := t' - (Nat.floor t : ℝ)) hs hs'' hmain'
    have hcast : (Nat.floor t : ℝ) = (Nat.floor t' : ℝ) := by exact_mod_cast heq
    exact ⟨by linarith [h2.1], h2.2⟩
  · have h1 := C.hdisj (k := Nat.floor t') (k' := Nat.floor t) (θ := θ')
      (s := t' - (Nat.floor t' : ℝ)) (θ' := θ) (s' := t - (Nat.floor t : ℝ))
      hgt hs' hs hmain.symm
    linarith [h1.1]

/-! ## Continuity of a two-branch function -/

/-- If `f` and `g` are continuous at `x₀` and agree there, then any pointwise choice between them
is continuous at `x₀`. -/
theorem continuousAt_if_of_eq {X : Type*} [PseudoMetricSpace X] {Y : Type*} [PseudoMetricSpace Y]
    {f g : X → Y} {x₀ : X} (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) (hfg : f x₀ = g x₀)
    (q : X → Prop) [DecidablePred q] :
    ContinuousAt (fun x => if q x then f x else g x) x₀ := by
  have hval : (if q x₀ then f x₀ else g x₀) = f x₀ := by
    by_cases h : q x₀
    · simp only [h, if_true]
    · simp only [h, if_false]; exact hfg.symm
  rw [Metric.continuousAt_iff] at hf hg ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => ?_⟩
  rw [hval]
  have hx₁ : dist x x₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : dist x x₀ < δ₂ := lt_of_lt_of_le hx (min_le_right _ _)
  by_cases hq : q x
  · simp only [hq, if_true]; exact h₁ hx₁
  · simp only [hq, if_false]
    rw [hfg]
    exact h₂ hx₂

/-! ## Continuity of the glued chain map -/

theorem Psi_continuousAt (C : ChainData γ Φ p) (θ t : ℝ) :
    ContinuousAt (fun u : ℝ × ℝ => C.Psi u.1 u.2) (θ, t) := by
  have hbranch : ∀ (k : ℕ) (c : ℝ),
      ContinuousAt (fun u : ℝ × ℝ => Φ k (u.1, u.2 - c)) (θ, t) := by
    intro k c
    exact (C.hcont k).continuousAt.comp
      (continuousAt_fst.prodMk (continuousAt_snd.sub continuousAt_const))
  rcases lt_or_ge t 0 with ht | ht
  · -- `t < 0`: the floor is `0` nearby, and the value is `Φ 0 (θ,t)`
    have hev : (fun u : ℝ × ℝ => C.Psi u.1 u.2) =ᶠ[nhds (θ, t)]
        (fun u : ℝ × ℝ => Φ 0 (u.1, u.2 - 0)) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds
        (show t < (1 : ℝ) by linarith)] with u hu
      have hf : Nat.floor u.2 = 0 := Nat.floor_eq_zero.mpr hu
      simp only [Psi, hf, Nat.cast_zero, sub_zero]
    exact (hbranch 0 0).congr hev.symm
  · set k : ℕ := Nat.floor t with hk
    have hkle : (k : ℝ) ≤ t := by rw [hk]; exact Nat.floor_le ht
    have hklt : t < (k : ℝ) + 1 := by rw [hk]; exact Nat.lt_floor_add_one t
    rcases lt_or_eq_of_le hkle with hlt | heq
    · -- `t` is not an integer: the floor is `k` nearby
      have hev : (fun u : ℝ × ℝ => C.Psi u.1 u.2) =ᶠ[nhds (θ, t)]
          (fun u : ℝ × ℝ => Φ k (u.1, u.2 - k)) := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hlt,
          (isOpen_lt continuous_snd continuous_const).mem_nhds hklt] with u hu1 hu2
        have hf : Nat.floor u.2 = k :=
          (Nat.floor_eq_iff (by linarith)).mpr ⟨le_of_lt hu1, hu2⟩
        simp only [Psi, hf]
      exact (hbranch k k).congr hev.symm
    · have htk : t = (k : ℝ) := heq.symm
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · -- `t = 0`: the floor is `0` on `{u | u.2 < 1}`
        have ht0 : t = 0 := by rw [htk, hk0]; norm_num
        have hev : (fun u : ℝ × ℝ => C.Psi u.1 u.2) =ᶠ[nhds (θ, t)]
            (fun u : ℝ × ℝ => Φ 0 (u.1, u.2 - 0)) := by
          filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds
            (show t < (1 : ℝ) by rw [ht0]; norm_num)] with u hu
          have hf : Nat.floor u.2 = 0 := Nat.floor_eq_zero.mpr hu
          simp only [Psi, hf, Nat.cast_zero, sub_zero]
        exact (hbranch 0 0).congr hev.symm
      · -- `t = k` an integer `≥ 1`: two branches, agreeing at `(θ,k)`
        have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        have hB1 : ContinuousAt (fun u : ℝ × ℝ => Φ k (u.1, u.2 - k)) (θ, t) := hbranch k k
        have hB2 : ContinuousAt (fun u : ℝ × ℝ => Φ (k - 1) (u.1, u.2 - ((k - 1 : ℕ) : ℝ)))
            (θ, t) := hbranch (k - 1) ((k - 1 : ℕ) : ℝ)
        have hagree : (fun u : ℝ × ℝ => Φ (k - 1) (u.1, u.2 - ((k - 1 : ℕ) : ℝ))) (θ, t)
            = (fun u : ℝ × ℝ => Φ k (u.1, u.2 - k)) (θ, t) := by
          show Φ (k - 1) (θ, t - ((k - 1 : ℕ) : ℝ)) = Φ k (θ, t - (k : ℝ))
          have h1 : t - (k : ℝ) = 0 := by rw [htk]; ring
          have h2 : t - ((k - 1 : ℕ) : ℝ) = 1 := by rw [hk1, htk]; ring
          rw [h1, h2, ← C.hmatch (k - 1) θ]
          exact congrArg (fun j => Φ j (θ, 0)) (by omega : k - 1 + 1 = k)
        have hev : (fun u : ℝ × ℝ => C.Psi u.1 u.2) =ᶠ[nhds (θ, t)]
            (fun u : ℝ × ℝ => if u.2 < t then Φ (k - 1) (u.1, u.2 - ((k - 1 : ℕ) : ℝ))
              else Φ k (u.1, u.2 - k)) := by
          have hlt_k : ((k - 1 : ℕ) : ℝ) < (k : ℝ) := by rw [hk1]; linarith
          have hnb1 : {u : ℝ × ℝ | ((k - 1 : ℕ) : ℝ) < u.2} ∈ nhds (θ, t) :=
            (isOpen_lt continuous_const continuous_snd).mem_nhds (by rw [htk]; exact hlt_k)
          have hnb2 : {u : ℝ × ℝ | u.2 < (k : ℝ) + 1} ∈ nhds (θ, t) :=
            (isOpen_lt continuous_snd continuous_const).mem_nhds
              (by rw [htk]; exact lt_add_one (k : ℝ))
          filter_upwards [hnb1, hnb2] with u hu1 hu2
          by_cases hcase : u.2 < t
          · have hf : Nat.floor u.2 = k - 1 :=
              (Nat.floor_eq_iff (by linarith)).mpr
                ⟨le_of_lt hu1, by rw [hk1]; linarith [hcase, htk]⟩
            rw [if_pos hcase]
            simp only [Psi, hf]
          · have hf : Nat.floor u.2 = k :=
              (Nat.floor_eq_iff (by linarith)).mpr
                ⟨by rw [htk] at hcase; linarith, hu2⟩
            rw [if_neg hcase]
            simp only [Psi, hf]
        exact (continuousAt_if_of_eq hB2 hB1 hagree (fun u : ℝ × ℝ => u.2 < t)).congr hev.symm

theorem Psi_continuous (C : ChainData γ Φ p) :
    Continuous (fun u : ℝ × ℝ => C.Psi u.1 u.2) :=
  continuous_iff_continuousAt.mpr fun u => C.Psi_continuousAt u.1 u.2

/-! ## The radial parametrisation of a tail -/

/-- The map on the disc whose value at `w ≠ 0` is `Ψ (arg w) (K + 1/‖w‖ - 1)`, and `p` at `0`. -/
def radial (C : ChainData γ Φ p) (K : ℕ) (w : Disc) : ℂ :=
  if (w : ℂ) = 0 then p else C.Psi (Complex.arg (w : ℂ)) (chainLevel K w)

/-- Every value of `radial K` other than `p` is attained by a cylinder `k ≥ K` at a parameter
with `s ∈ [0,1]`. -/
theorem radial_range_subset (C : ChainData γ Φ p) (K : ℕ) {q : ℂ}
    (hq : q ∈ Set.range (C.radial K)) :
    q = p ∨ ∃ (k : ℕ) (θ s : ℝ), K ≤ k ∧ s ∈ Set.Icc 0 1 ∧ Φ k (θ, s) = q := by
  obtain ⟨u, rfl⟩ := hq
  by_cases hu : (u : ℂ) = 0
  · exact Or.inl (by simp only [radial, if_pos hu])
  · refine Or.inr ⟨Nat.floor (chainLevel K u), Complex.arg (u : ℂ),
      chainLevel K u - (Nat.floor (chainLevel K u) : ℝ), le_floor_chainLevel K hu,
      C.Psi_frac_mem (chainLevel_nonneg K hu), ?_⟩
    simp only [radial, if_neg hu, Psi]

theorem radial_continuousAt_aux (C : ChainData γ Φ p) (K : ℕ) {w : Disc} (hw : (w : ℂ) ≠ 0) :
    ContinuousAt (fun u : Disc => C.Psi (Complex.arg (u : ℂ)) (chainLevel K u)) w := by
  have hT : ContinuousAt (fun u : Disc => chainLevel K u) w := by
    have hnorm : ContinuousAt (fun u : Disc => ‖(u : ℂ)‖) w :=
      continuous_subtype_val.norm.continuousAt
    have h3 : ContinuousAt (fun u : Disc => (‖(u : ℂ)‖)⁻¹) w :=
      hnorm.inv₀ (norm_ne_zero_iff.mpr hw)
    have h4 : ContinuousAt (fun u : Disc => 1 / ‖(u : ℂ)‖) w := by
      simpa only [one_div] using h3
    simp only [chainLevel]
    exact (h4.sub continuousAt_const).const_add ((K : ℝ))
  have h1 : ContinuousAt (fun q : ℂ × ℝ => C.Psi (Complex.arg q.1) q.2)
      ((w : ℂ), chainLevel K w) :=
    continuousAt_arg_lift (Φ := fun q : ℝ × ℝ => C.Psi q.1 q.2) C.Psi_continuous
      (fun t s => C.Psi_periodic t s) hw
  have h2 : ContinuousAt (fun u : Disc => ((u : ℂ), chainLevel K u)) w :=
    continuous_subtype_val.continuousAt.prodMk hT
  exact h1.comp (f := fun u : Disc => ((u : ℂ), chainLevel K u)) h2

theorem radial_continuous (C : ChainData γ Φ p) (K : ℕ) : Continuous (C.radial K) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : (w : ℂ) = 0
  · rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨K₀, hK₀⟩ := C.hshrink ε hε
    refine ⟨1 / ((K₀ : ℝ) + (K : ℝ) + 1), by positivity, fun u hu => ?_⟩
    have hwval : C.radial K w = p := by simp only [radial, if_pos hw]
    rw [hwval]
    by_cases hu0 : (u : ℂ) = 0
    · rw [show C.radial K u = p from by simp only [radial, if_pos hu0]]
      simpa using hε
    · have hnorm : ‖(u : ℂ)‖ < 1 / ((K₀ : ℝ) + (K : ℝ) + 1) := by
        have h1 : dist u w = dist (u : ℂ) (w : ℂ) := Subtype.dist_eq u w
        rw [h1, show (w : ℂ) = (0 : ℂ) from hw, dist_eq_norm, sub_zero] at hu
        exact hu
      have hpos : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr hu0
      have hbig : (K₀ : ℝ) + (K : ℝ) + 1 < 1 / ‖(u : ℂ)‖ := by
        have hδ : (1 : ℝ) / (1 / ((K₀ : ℝ) + (K : ℝ) + 1)) = (K₀ : ℝ) + (K : ℝ) + 1 :=
          one_div_one_div _
        rw [← hδ]
        exact one_div_lt_one_div_of_lt hpos hnorm
      have hfloor : K₀ ≤ Nat.floor (chainLevel K u) := by
        refine Nat.le_floor ?_
        simp only [chainLevel]
        linarith
      have hmem : chainLevel K u - (Nat.floor (chainLevel K u) : ℝ) ∈ Set.Icc 0 1 :=
        C.Psi_frac_mem (chainLevel_nonneg K hu0)
      have hfin := hK₀ (Nat.floor (chainLevel K u)) hfloor
        (Complex.arg (u : ℂ)) (chainLevel K u - (Nat.floor (chainLevel K u) : ℝ)) hmem
      rw [show C.radial K u = Φ (Nat.floor (chainLevel K u))
          (Complex.arg (u : ℂ), chainLevel K u - (Nat.floor (chainLevel K u) : ℝ))
        from by simp only [radial, if_neg hu0, Psi]]
      simpa only [dist_eq_norm] using hfin
  · have hnb : {u : Disc | (u : ℂ) ≠ 0} ∈ nhds w := by
      have hopen : IsOpen ((fun u : Disc => (u : ℂ)) ⁻¹' ({0}ᶜ : Set ℂ)) :=
        (isOpen_compl_iff.mpr isClosed_singleton).preimage continuous_subtype_val
      exact hopen.mem_nhds (by simpa using hw)
    refine (C.radial_continuousAt_aux K hw).congr ?_
    filter_upwards [hnb] with u hu
    simp only [radial, if_neg hu]

theorem radial_inj (C : ChainData γ Φ p) (K : ℕ)
    (hK : ∀ (k : ℕ) (θ s : ℝ), K ≤ k → s ∈ Set.Icc 0 1 → Φ k (θ, s) ≠ p) :
    Function.Injective (C.radial K) := by
  intro u v huv
  by_cases hu : (u : ℂ) = 0
  · rw [show C.radial K u = p from by simp only [radial, if_pos hu]] at huv
    by_cases hv : (v : ℂ) = 0
    · exact Subtype.ext (by rw [hu, hv])
    · exfalso
      rw [show C.radial K v = C.Psi (Complex.arg (v : ℂ)) (chainLevel K v) from by
        simp only [radial, if_neg hv]] at huv
      exact (hK (Nat.floor (chainLevel K v)) (Complex.arg (v : ℂ))
        (chainLevel K v - (Nat.floor (chainLevel K v) : ℝ))
        (le_floor_chainLevel K hv) (C.Psi_frac_mem (chainLevel_nonneg K hv)))
        (by simpa only [Psi] using huv.symm)
  · by_cases hv : (v : ℂ) = 0
    · rw [show C.radial K v = p from by simp only [radial, if_pos hv]] at huv
      exfalso
      rw [show C.radial K u = C.Psi (Complex.arg (u : ℂ)) (chainLevel K u) from by
        simp only [radial, if_neg hu]] at huv
      exact (hK (Nat.floor (chainLevel K u)) (Complex.arg (u : ℂ))
        (chainLevel K u - (Nat.floor (chainLevel K u) : ℝ))
        (le_floor_chainLevel K hu) (C.Psi_frac_mem (chainLevel_nonneg K hu)))
        (by simpa only [Psi] using huv)
    · have h1 : C.Psi (Complex.arg (u : ℂ)) (chainLevel K u)
          = C.Psi (Complex.arg (v : ℂ)) (chainLevel K v) := by
        simpa only [radial, if_neg hu, if_neg hv] using huv
      obtain ⟨hteq, m, hm⟩ := C.Psi_inj (chainLevel_nonneg K hu) (chainLevel_nonneg K hv) h1
      have hnorm : ‖(u : ℂ)‖ = ‖(v : ℂ)‖ := by
        have h2 : 1 / ‖(u : ℂ)‖ = 1 / ‖(v : ℂ)‖ := by
          simp only [chainLevel] at hteq
          linarith
        simp only [one_div] at h2
        exact inv_inj.mp h2
      have hexp : Complex.exp ((Complex.arg (v : ℂ) : ℝ) * Complex.I)
          = Complex.exp ((Complex.arg (u : ℂ) : ℝ) * Complex.I) := by
        rw [hm]
        have h2 : (((Complex.arg (u : ℂ) : ℝ) + (m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
            = (Complex.arg (u : ℂ) : ℂ) * Complex.I
              + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          push_cast; ring
        rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have hq : (u : ℂ) = (v : ℂ) := by
        calc (u : ℂ)
            = (‖(u : ℂ)‖ : ℂ) * Complex.exp ((Complex.arg (u : ℂ) : ℝ) * Complex.I) :=
              (Complex.norm_mul_exp_arg_mul_I (u : ℂ)).symm
          _ = (‖(v : ℂ)‖ : ℂ) * Complex.exp ((Complex.arg (v : ℂ) : ℝ) * Complex.I) := by
              rw [hnorm, ← hexp]
          _ = (v : ℂ) := Complex.norm_mul_exp_arg_mul_I (v : ℂ)
      exact Subtype.ext hq

/-! ## The point `p` is not attained -/

/-- If `p` is attained with parameter `s₀ < 1`, then no cylinder from `k₀ + 2` on attains it. -/
theorem not_hit_aux (C : ChainData γ Φ p) (k₀ : ℕ) (θ₀ s₀ : ℝ)
    (hs₀ : s₀ ∈ Set.Icc 0 1) (hs₀lt : s₀ < 1) (hp : Φ k₀ (θ₀, s₀) = p) :
    ∀ (k : ℕ) (θ s : ℝ), k₀ + 2 ≤ k → s ∈ Set.Icc 0 1 → Φ k (θ, s) ≠ p := by
  intro k θ s hk hs hEq
  have h1 := C.hdisj (k := k₀) (k' := k) (θ := θ₀) (s := s₀) (θ' := θ) (s' := s)
    (by omega) hs₀ hs (by rw [hp, hEq])
  linarith [h1.1]

/-- **The point `p` is not attained by the chain.** -/
theorem not_hit (C : ChainData γ Φ p) (k : ℕ) (θ s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    Φ k (θ, s) ≠ p := by
  suffices h : ∀ (k : ℕ) (θ s : ℝ), s ∈ Set.Icc 0 1 → s < 1 → Φ k (θ, s) ≠ p by
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact h k θ s hs hlt
    · rw [heq]
      have h1 := h (k + 1) θ 0 (by norm_num) (by norm_num)
      rwa [C.hmatch k θ] at h1
  intro k θ s hs hlt hEq
  set K : ℕ := k + 2 with hK
  have hKnot : ∀ (k' : ℕ) (θ' s' : ℝ), K ≤ k' → s' ∈ Set.Icc 0 1 → Φ k' (θ', s') ≠ p := by
    intro k' θ' s' hk' hs'
    exact C.not_hit_aux k θ s hs hlt hEq k' θ' s' (by omega) hs'
  have hinj : Function.Injective (C.radial K) := C.radial_inj K hKnot
  have hInt : p ∈ interior (Set.range (C.radial K)) := by
    have himg := Work.Smooth.SphereJordan.mem_interior_image_of_norm_lt_one
      (⟨C.radial K, C.radial_continuous K⟩ : C(Disc, ℂ)) hinj 0 (by simp)
    have h0 : (⟨C.radial K, C.radial_continuous K⟩ : C(Disc, ℂ)) 0 = p := by
      simp only [ContinuousMap.coe_mk]
      simp [radial]
    rw [h0] at himg
    refine interior_mono ?_ himg
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hInt)
  have hcontε : ContinuousAt (fun ε : ℝ => Φ k (θ + ε, s)) 0 := by
    have h1 : ContinuousAt (fun ε : ℝ => (θ + ε, s)) 0 :=
      (continuousAt_const.add continuousAt_id).prodMk continuousAt_const
    exact (C.hcont k).continuousAt.comp h1
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hcontε δ hδpos
  set ε₀ : ℝ := min η (2 * Real.pi) / 2 with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact half_pos (lt_min hηpos (by positivity))
  have hε₀ltη : ε₀ < η := by
    have h : min η (2 * Real.pi) ≤ η := min_le_left _ _
    rw [hε₀def]
    linarith
  have hε₀lt : ε₀ < 2 * Real.pi := by
    have h : min η (2 * Real.pi) ≤ 2 * Real.pi := min_le_right _ _
    rw [hε₀def]
    linarith [Real.pi_pos]
  have hq : Φ k (θ + ε₀, s) ≠ p := by
    intro hqp
    have h3 := C.hinj (k := k) (θ := θ + ε₀) (s := s) (θ' := θ) (s' := s)
      hs hs (by rw [hqp, hEq])
    obtain ⟨m, hm⟩ := h3.2
    have hm' : (m : ℝ) * (2 * Real.pi) = -ε₀ := by linarith [hm]
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · have hle : (m : ℝ) ≤ -1 := by
          have : m ≤ -1 := by omega
          exact_mod_cast this
        nlinarith [Real.pi_pos, hε₀lt, hm']
      · exact h
      · have hle : (1 : ℝ) ≤ (m : ℝ) := by
          have : 1 ≤ m := by omega
          exact_mod_cast this
        nlinarith [Real.pi_pos, hε₀pos, hm']
    have hzero : ε₀ = 0 := by
      rw [hm0] at hm'
      have h0 : (0 : ℝ) = -ε₀ := by simpa using hm'
      linarith
    exact (ne_of_gt hε₀pos) hzero
  have hdist : dist (Φ k (θ + ε₀, s)) p < δ := by
    have h1 : dist (Φ k (θ + ε₀, s)) (Φ k (θ + 0, s)) < δ :=
      hη (x := ε₀) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε₀pos]; exact hε₀ltη)
    simpa only [add_zero, hEq] using h1
  have hmem : Φ k (θ + ε₀, s) ∈ Set.range (C.radial K) :=
    hδsub (Metric.mem_ball.mpr hdist)
  rcases C.radial_range_subset K hmem with hp | ⟨k', θ', s', hk', hs', hEq'⟩
  · exact hq hp
  · have h2 := C.hdisj (k := k) (k' := k') (θ := θ + ε₀) (s := s) (θ' := θ') (s' := s')
      (by omega) hs hs' (by rw [hEq'])
    linarith [h2.1]

/-! ## The disc extension -/

theorem discExtension_of_chainData (C : ChainData γ Φ p) :
    DiscExtension ⟨γ, C.cont, C.per⟩ := by
  have hp : ∀ (k : ℕ) (θ s : ℝ), s ∈ Set.Icc 0 1 → Φ k (θ, s) ≠ p :=
    fun k θ s hs => C.not_hit k θ s hs
  refine ⟨⟨C.radial 0, C.radial_continuous 0⟩, ?_, ?_⟩
  · exact C.radial_inj 0 (fun k θ s _ hs => hp k θ s hs)
  · intro θ
    have hne : ((circlePoint θ : Disc) : ℂ) ≠ 0 := by
      rw [circlePoint_coe]; exact Complex.exp_ne_zero _
    change C.radial 0 (circlePoint θ) = γ θ
    rw [show C.radial 0 (circlePoint θ)
        = C.Psi (Complex.arg ((circlePoint θ : Disc) : ℂ)) (chainLevel 0 (circlePoint θ))
      from by simp only [radial, if_neg hne]]
    have hT : chainLevel 0 (circlePoint θ) = ((0 : ℕ) : ℝ) := by
      have h0 : chainLevel 0 (circlePoint θ) = 0 := by
        simp only [chainLevel, Nat.cast_zero, zero_add]
        rw [norm_circlePoint θ]
        norm_num
      rw [h0]
      norm_num
    rw [hT, C.Psi_natCast 0, C.hzero]
    refine eq_of_exp_eq_periodic C.per ?_
    rw [circlePoint_coe, exp_arg_mul_I_eq _ (Complex.exp_ne_zero _),
      Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one]

end ChainData

theorem discExtension_of_cylinder_chain
    (γ : ℝ → ℂ) (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (Φ : ℕ → ℝ × ℝ → ℂ) (p : ℂ)
    (hcont : ∀ k, Continuous (Φ k))
    (hper : ∀ (k : ℕ) (θ s : ℝ), Φ k (θ + 2 * Real.pi, s) = Φ k (θ, s))
    (hzero : ∀ θ : ℝ, Φ 0 (θ, 0) = γ θ)
    (hmatch : ∀ (k : ℕ) (θ : ℝ), Φ (k + 1) (θ, 0) = Φ k (θ, 1))
    (hinj : ∀ (k : ℕ) (θ s θ' s' : ℝ), s ∈ Set.Icc 0 1 → s' ∈ Set.Icc 0 1 →
        Φ k (θ, s) = Φ k (θ', s') → s = s' ∧ ∃ m : ℤ, θ' = θ + m * (2 * Real.pi))
    (hdisj : ∀ (k k' : ℕ) (θ s θ' s' : ℝ), k < k' → s ∈ Set.Icc 0 1 → s' ∈ Set.Icc 0 1 →
        Φ k (θ, s) = Φ k' (θ', s') →
        s = 1 ∧ s' = 0 ∧ ∃ m : ℤ, θ' = θ + m * (2 * Real.pi))
    (hshrink : ∀ ε > 0, ∃ K, ∀ k ≥ K, ∀ (θ s : ℝ), s ∈ Set.Icc 0 1 → ‖Φ k (θ, s) - p‖ < ε) :
    DiscExtension ⟨γ, hγc, hγp⟩ :=
  ChainData.discExtension_of_chainData (γ := γ) (Φ := Φ) (p := p)
    { cont := hγc, per := hγp, hcont := hcont, hper := hper, hzero := hzero, hmatch := hmatch,
      hinj := hinj, hdisj := hdisj, hshrink := hshrink }

end

end Work.Smooth.JordanSeparation
