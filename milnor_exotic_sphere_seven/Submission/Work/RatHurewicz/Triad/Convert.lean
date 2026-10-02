import Mathlib
import Submission.Work.RatHurewicz.Triad.Basic
import Submission.Work.RatHurewicz.PinchGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From a homotopy of pairs to a homotopy relative to the boundary

tom Dieck, *Algebraic Topology*, Proposition (6.7.2): if a map of pairs
`f : (D^n, S^{n-1}) → (Y, A)` is homotopic *as a map of pairs* to a map with image in `A`, then it
is homotopic to such a map *relative to* `S^{n-1}`.

Here is the explicit cube-level construction.  Write `ρ(x) = max_i |2 x_i - 1| ∈ [0,1]` for the
ℓ∞-radius about the centre (`Work.RatHurewicz.sig`), so that `ρ(x) = 1 ↔ x ∈ ∂I^d`.  Given the
homotopy `G : I^d × I → Y` of pairs, put

`Ψ(x,t) = (c + λ(x,t)(x - c), t·θ(x))`,  `λ = 1/max(ρ, 1-t/2)`,  `θ = min 1 (max 0 (2-2ρ))`,

where `c = (1/2,…,1/2)`.  Then `Ψ(·,0) = id`, `Ψ` fixes `∂I^d × I` (because `ρ = 1` there gives
`λ = 1`, `θ = 0`), and `Ψ(·,1)` lands either in `∂I^d × I` — for `ρ ≥ 1/2`, where `λρ = 1` — or in
`I^d × {1}` — for `ρ < 1/2`, where `θ = 1`.  Hence `G ∘ Ψ` is the required homotopy relative to
the boundary.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

noncomputable section

open Work.Stems.Cubical

/-- The `ℓ∞`-radius about the centre of the cube.  It takes the value `1` exactly on the boundary
of the cube. -/
def rhoR {d : ℕ} (hd : 1 ≤ d) (x : ICube d) : ℝ := sig d hd x

theorem continuous_rhoR {d : ℕ} (hd : 1 ≤ d) : Continuous (rhoR hd) :=
  continuous_sig d hd

theorem rhoR_nonneg {d : ℕ} (hd : 1 ≤ d) (x : ICube d) : 0 ≤ rhoR hd x :=
  sig_nonneg d hd x

theorem rhoR_le_one {d : ℕ} (hd : 1 ≤ d) (x : ICube d) : rhoR hd x ≤ 1 :=
  sig_le_one d hd x

theorem rhoR_eq_one_iff {d : ℕ} (hd : 1 ≤ d) {x : ICube d} :
    rhoR hd x = 1 ↔ x ∈ Cube.boundary (Fin d) := sig_eq_one_iff d hd x

theorem abs_le_rhoR {d : ℕ} (hd : 1 ≤ d) (x : ICube d) (i : Fin d) :
    |2 * (x i : ℝ) - 1| ≤ rhoR hd x := sig_le d hd x i

/-- The scaling factor `λ` of the conversion. -/
def lamConv {d : ℕ} (hd : 1 ≤ d) (x : ICube d) (t : I) : ℝ :=
  1 / max (rhoR hd x) (1 - (t : ℝ) / 2)

/-- The "time" factor `θ` of the conversion. -/
def thR {d : ℕ} (hd : 1 ≤ d) (x : ICube d) : ℝ := min 1 (max 0 (2 - 2 * rhoR hd x))

theorem lamConv_denom_pos {d : ℕ} (hd : 1 ≤ d) (x : ICube d) (t : I) :
    (0:ℝ) < max (rhoR hd x) (1 - (t : ℝ) / 2) := by
  have ht : (t : ℝ) ≤ 1 := t.2.2
  have h3 : (1:ℝ) / 2 ≤ 1 - (t : ℝ) / 2 := by linarith
  exact lt_of_lt_of_le (by norm_num) (le_trans h3 (le_max_right _ _))

theorem lamConv_pos {d : ℕ} (hd : 1 ≤ d) (x : ICube d) (t : I) : 0 < lamConv hd x t :=
  div_pos one_pos (lamConv_denom_pos hd x t)

theorem continuous_lamConv {d : ℕ} (hd : 1 ≤ d) :
    Continuous fun p : ICube d × I => lamConv hd p.1 p.2 := by
  unfold lamConv
  refine Continuous.div continuous_const ?_ fun p => ne_of_gt (lamConv_denom_pos hd p.1 p.2)
  exact ((continuous_rhoR hd).comp continuous_fst).max
    (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).div_const 2))

theorem continuous_thR {d : ℕ} (hd : 1 ≤ d) :
    Continuous fun p : ICube d × I => thR hd p.1 := by
  unfold thR
  exact continuous_const.min (continuous_const.max
    (continuous_const.sub (continuous_const.mul ((continuous_rhoR hd).comp continuous_fst))))

theorem lamConv_le_inv_rho {d : ℕ} (hd : 1 ≤ d) (x : ICube d) (t : I) (h : 0 < rhoR hd x) :
    lamConv hd x t ≤ 1 / rhoR hd x := by
  unfold lamConv
  exact one_div_le_one_div_of_le h (le_max_left _ _)

theorem lamConv_zero {d : ℕ} (hd : 1 ≤ d) (x : ICube d) : lamConv hd x 0 = 1 := by
  have h : max (rhoR hd x) (1 - ((0 : I) : ℝ) / 2) = 1 := by
    rw [show (1 - ((0 : I) : ℝ) / 2) = 1 by norm_num]
    exact max_eq_right (rhoR_le_one hd x)
  rw [lamConv, h]
  norm_num

theorem thR_eq_zero_of_rho_one {d : ℕ} (hd : 1 ≤ d) {x : ICube d} (h : rhoR hd x = 1) :
    thR hd x = 0 := by
  rw [thR, h]
  norm_num

theorem thR_eq_one_of_lt {d : ℕ} (hd : 1 ≤ d) {x : ICube d} (h : rhoR hd x < 1 / 2) :
    thR hd x = 1 := by
  rw [thR]
  refine min_eq_left ?_
  refine le_trans (by linarith : (1:ℝ) ≤ 2 - 2 * rhoR hd x) (le_max_right _ _)

/-- A point of `I` together with the two inequalities that define it. -/
theorem abs_sub_half_le {d : ℕ} (hd : 1 ≤ d) (x : ICube d) (i : Fin d) :
    |(x i : ℝ) - 1 / 2| ≤ rhoR hd x / 2 := by
  have h := abs_le_rhoR hd x i
  have h2 : 2 * ((x i : ℝ) - 1 / 2) = 2 * (x i : ℝ) - 1 := by ring
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem lam_mul_rho_le_one {d : ℕ} (hd : 1 ≤ d) (x : ICube d) (t : I) :
    lamConv hd x t * rhoR hd x ≤ 1 := by
  rcases eq_or_lt_of_le (rhoR_nonneg hd x) with h | h
  · rw [← h]; simp
  · have h1 := lamConv_le_inv_rho hd x t h
    have h2 : 0 ≤ lamConv hd x t := le_of_lt (lamConv_pos hd x t)
    calc lamConv hd x t * rhoR hd x ≤ (1 / rhoR hd x) * rhoR hd x := by
          exact mul_le_mul_of_nonneg_right h1 (rhoR_nonneg hd x)
      _ = 1 := by field_simp

theorem thR_mem {d : ℕ} (hd : 1 ≤ d) (x : ICube d) : thR hd x ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- **The explicit reparametrisation `Ψ` of tom Dieck (6.7.2).** -/
def psiCM {d : ℕ} (hd : 1 ≤ d) : C(ICube d × I, ICube d × I) where
  toFun p :=
    (fun i => ⟨1 / 2 + lamConv hd p.1 p.2 * ((p.1 i : ℝ) - 1 / 2), by
        have h1 := abs_sub_half_le hd p.1 i
        have h2 := lam_mul_rho_le_one hd p.1 p.2
        have h3 : 0 ≤ lamConv hd p.1 p.2 := le_of_lt (lamConv_pos hd p.1 p.2)
        have h4 : lamConv hd p.1 p.2 * |(p.1 i : ℝ) - 1 / 2| ≤ 1 / 2 := by
          calc lamConv hd p.1 p.2 * |(p.1 i : ℝ) - 1 / 2|
              ≤ lamConv hd p.1 p.2 * (rhoR hd p.1 / 2) :=
                mul_le_mul_of_nonneg_left h1 h3
            _ = (lamConv hd p.1 p.2 * rhoR hd p.1) / 2 := by ring
            _ ≤ 1 / 2 := by linarith
        have h5 : |lamConv hd p.1 p.2 * ((p.1 i : ℝ) - 1 / 2)| ≤ 1 / 2 := by
          rw [abs_mul, abs_of_nonneg h3]; exact h4
        rw [abs_le] at h5
        constructor <;> linarith [h5.1, h5.2]⟩,
      ⟨(p.2 : ℝ) * thR hd p.1, by
        have h1 := thR_mem hd p.1
        have ht0 : (0:ℝ) ≤ (p.2 : ℝ) := p.2.2.1
        have ht1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
        exact ⟨mul_nonneg ht0 h1.1, mul_le_one₀ ht1 h1.1 h1.2⟩⟩)
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_pi fun i => Continuous.subtype_mk ?_ _
      exact continuous_const.add ((continuous_lamConv hd).mul
        ((continuous_subtype_val.comp (continuous_apply i |>.comp continuous_fst)).sub
          continuous_const))
    · refine Continuous.subtype_mk ?_ _
      exact (continuous_subtype_val.comp continuous_snd).mul (continuous_thR hd)

@[simp] theorem psiCM_apply_fst {d : ℕ} (hd : 1 ≤ d) (p : ICube d × I) (i : Fin d) :
    ((psiCM hd p).1 i : ℝ) = 1 / 2 + lamConv hd p.1 p.2 * ((p.1 i : ℝ) - 1 / 2) := rfl

@[simp] theorem psiCM_apply_snd {d : ℕ} (hd : 1 ≤ d) (p : ICube d × I) :
    ((psiCM hd p).2 : ℝ) = (p.2 : ℝ) * thR hd p.1 := rfl

theorem psiCM_zero {d : ℕ} (hd : 1 ≤ d) (x : ICube d) : psiCM hd (x, 0) = (x, 0) := by
  refine Prod.ext ?_ ?_
  · funext i
    apply Subtype.ext
    simp [lamConv_zero]
  · apply Subtype.ext
    simp

theorem psiCM_wall {d : ℕ} (hd : 1 ≤ d) {x : ICube d} (hx : x ∈ Cube.boundary (Fin d))
    (t : I) : psiCM hd (x, t) = (x, 0) := by
  have hρ : rhoR hd x = 1 := (rhoR_eq_one_iff hd).mpr hx
  have hlam : lamConv hd x t = 1 := by
    rw [lamConv, hρ]
    rw [max_eq_left]
    · norm_num
    · have ht : (0:ℝ) ≤ (t:ℝ) := t.2.1
      linarith
  refine Prod.ext ?_ ?_
  · funext i
    apply Subtype.ext
    simp [hlam]
  · apply Subtype.ext
    simp [thR_eq_zero_of_rho_one hd hρ]

theorem psiCM_one {d : ℕ} (hd : 1 ≤ d) (x : ICube d) :
    (psiCM hd (x, 1)).1 ∈ Cube.boundary (Fin d) ∨ ((psiCM hd (x, 1)).2 : ℝ) = 1 := by
  rcases lt_or_ge (rhoR hd x) (1 / 2 : ℝ) with h | h
  · right
    have hth : thR hd x = 1 := thR_eq_one_of_lt hd h
    rw [psiCM_apply_snd]
    rw [show ((1 : I) : ℝ) = 1 by norm_num, hth, mul_one]
  · left
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun i => |2 * (x i : ℝ) - 1|)
    have hρ : rhoR hd x = |2 * (x i₀ : ℝ) - 1| := by
      rw [rhoR, sig_def]; exact hi₀
    have hρpos : 0 < rhoR hd x := by linarith
    have hlam : lamConv hd x 1 = 1 / rhoR hd x := by
      rw [lamConv]
      rw [show (1 - ((1 : I) : ℝ) / 2) = 1 / 2 by norm_num]
      rw [max_eq_left h]
    have hcoord : ((psiCM hd (x, 1)).1 i₀ : ℝ)
        = 1 / 2 + (1 / rhoR hd x) * ((x i₀ : ℝ) - 1 / 2) := by
      rw [psiCM_apply_fst, hlam]
    refine ⟨i₀, ?_⟩
    have hkey : (2 * (x i₀ : ℝ) - 1) / rhoR hd x = 1 ∨ (2 * (x i₀ : ℝ) - 1) / rhoR hd x = -1 := by
      rcases abs_cases (2 * (x i₀ : ℝ) - 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have hthis : rhoR hd x = 2 * (x i₀ : ℝ) - 1 := hρ.trans h1
        have hne : (2 * (x i₀ : ℝ) - 1) ≠ 0 := by rw [← hthis]; exact ne_of_gt hρpos
        rw [hthis]
        exact div_self hne
      · right
        have : (2 * (x i₀ : ℝ) - 1) = -rhoR hd x := by
          have := hρ.trans h1
          linarith
        rw [this, neg_div, div_self (ne_of_gt hρpos)]
    have hsplit : ((psiCM hd (x, 1)).1 i₀ : ℝ)
        = 1 / 2 + (2 * (x i₀ : ℝ) - 1) / (2 * rhoR hd x) := by
      rw [hcoord]
      have hne : rhoR hd x ≠ 0 := ne_of_gt hρpos
      field_simp
    have hhalf : ∀ c : ℝ, (2 * (x i₀ : ℝ) - 1) / (2 * rhoR hd x) = c
        → ((psiCM hd (x, 1)).1 i₀ : ℝ) = 1 / 2 + c := by
      intro c hc
      rw [hsplit, hc]
    rcases hkey with hk | hk
    · right
      apply Subtype.ext
      rw [hhalf (1/2) (by
        rw [show (2 * (x i₀ : ℝ) - 1) / (2 * rhoR hd x)
          = ((2 * (x i₀ : ℝ) - 1) / rhoR hd x) / 2 by ring, hk])]
      norm_num
    · left
      apply Subtype.ext
      rw [hhalf (-1/2) (by
        rw [show (2 * (x i₀ : ℝ) - 1) / (2 * rhoR hd x)
          = ((2 * (x i₀ : ℝ) - 1) / rhoR hd x) / 2 by ring, hk])]
      norm_num

/-- **tom Dieck (6.7.2), cube form.**  If a map `f : I^d → Y` of pairs is homotopic *as a map of
pairs* to a map with values in `A`, then it is homotopic to such a map *relative to* `∂I^d`. -/
theorem compressRel_of_homotopyPairs {Y : Type} [TopologicalSpace Y] {A : Set Y} {d : ℕ}
    (f : C(ICube d, Y)) (G : C(ICube d × I, Y))
    (hG0 : ∀ x, G (x, 0) = f x)
    (hGbd : ∀ x, x ∈ Cube.boundary (Fin d) → ∀ t, G (x, t) ∈ A)
    (hG1 : ∀ x, G (x, 1) ∈ A) :
    ∃ H : C(ICube d × I, Y),
      (∀ x, H (x, 0) = f x) ∧
      (∀ x (hx : x ∈ Cube.boundary (Fin d)) t, H (x, t) = f x) ∧
      (∀ x, H (x, 1) ∈ A) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨G, fun x => hG0 x, fun x hx t => by
      obtain ⟨i, -⟩ := hx
      exact i.elim0, hG1⟩
  · refine ⟨G.comp (psiCM hd), ?_, ?_, ?_⟩
    · intro x
      rw [ContinuousMap.comp_apply, psiCM_zero, hG0]
    · intro x hx t
      rw [ContinuousMap.comp_apply, psiCM_wall hd hx t, hG0]
    · intro x
      rcases psiCM_one hd x with h | h
      · simpa only [ContinuousMap.comp_apply, Prod.mk.eta] using
          hGbd (psiCM hd (x, 1)).1 h (psiCM hd (x, 1)).2
      · have h' : (psiCM hd (x, 1)).2 = 1 := Subtype.ext h
        have h2 : psiCM hd (x, 1) = ((psiCM hd (x, 1)).1, (1 : I)) := Prod.ext rfl h'
        rw [ContinuousMap.comp_apply, h2]
        exact hG1 _

end

end Work.RatHurewicz.Triad
