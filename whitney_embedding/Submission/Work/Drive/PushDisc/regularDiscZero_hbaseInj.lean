import Mathlib
import Submission.Work.Drive.PushDisc.regularDiscDefs

namespace Work.Drive.PushDisc

open Set Metric

/-!
# Base injectivity of `Δ₀` on the lens

`regularDiscZero D A B g δ` is the base map `Δ₀` of the lead's `L0` (see
`regularDiscDefs.lean`): with `A` (the plane arc), `B` (the finger arc) and the Hadamard quotient
`g` of `B - A`, it is `Δ₀ (x,y) = A x + y • g x` plus the correction that replaces the chord by the
Whitney disc `D` on the bulk of the lens, cut off near the two cusps and on the two edges.

The result proved here is the *base injectivity* used by the generic-perturbation step: two distinct
points of the lens which are not separated by the four bumps (`lensBump ρ k`, `k : Fin 2 × Fin 2`)
are already separated by `Δ₀`.  Equivalently, the map `p ↦ (Δ₀ p, (lensBump ρ k p)_k)` is injective
on the lens.

The content is entirely combinatorial:

* on the open lens the two `x`-bumps and the two `y`-bumps separate the point
  (`lensBump_sep`, in `lensRegularDefs.lean`);
* every point of the closed lens *off* the open lens lies on the bottom edge `y = 0` or on the arch
  `y = arch x` (a cusp point satisfies both), and all four bumps vanish there;
* on the bottom edge `Δ₀ = A`, on the arch `Δ₀ = B`, so the edge hypotheses `hinjA`, `hinjB` and the
  disjointness `hdisj` of the two edges (which allows `A` and `B` to meet only at the two cusps)
  finish the job.

No hypothesis on the disc `D` beyond its two edge rows is used.
-/

/-- A point of the closed lens which is not in the open lens lies on the bottom edge `y = 0` or on
the arch `y = arch x`. -/
private theorem lens_snd_eq_zero_or_eq_arch {p : ℝ × ℝ} (hp : p ∈ lens) (hpi : p ∉ lensOpen) :
    p.2 = 0 ∨ p.2 = arch p.1 := by
  rw [lens, Set.mem_ofPred_eq] at hp
  rw [lensOpen, Set.mem_ofPred_eq] at hpi
  obtain ⟨hp1, hp2, hp3⟩ := hp
  by_cases hxa : |p.1| < 1
  · by_cases hy0 : 0 < p.2
    · right
      by_contra hne
      exact hpi ⟨hxa, hy0, lt_of_le_of_ne hp3 hne⟩
    · left; linarith
  · left
    have hge : 1 ≤ |p.1| := le_of_not_gt hxa
    have habs : |p.1| = 1 := le_antisymm hp1 hge
    have hsq : p.1 ^ 2 = 1 := by rw [← sq_abs, habs]; norm_num
    have harch : arch p.1 = 0 := by simp only [arch]; linarith
    linarith

/-- Every bump vanishes at a point of the closed lens which is not in the open lens. -/
private theorem lensBump_eq_zero_of_not_mem_lensOpen {ρ : ℝ} {p : ℝ × ℝ} (hp : p ∈ lens)
    (hpi : p ∉ lensOpen) (k : Fin 2 × Fin 2) : lensBump ρ k p = 0 := by
  rcases lens_snd_eq_zero_or_eq_arch hp hpi with h | h
  · rw [show p = (p.1, 0) from Prod.ext rfl h]
    exact lensBump_eq_zero_bot ρ k p.1
  · rw [show p = (p.1, arch p.1) from Prod.ext rfl h]
    exact lensBump_eq_zero_top ρ k p.1

/-- The `(0,0)`-bump is strictly positive on the open lens. -/
private theorem lensBump_zero_zero_pos {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ × ℝ} (hp : p ∈ lensOpen) :
    0 < lensBump ρ ((0 : Fin 2), (0 : Fin 2)) p := by
  rw [lensOpen, Set.mem_ofPred_eq] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  show 0 < lensChi ρ p.1 * lensAlpha (0 : Fin 2) p.1 * lensZeta (0 : Fin 2) p.2 (arch p.1)
  have hchi : 0 < lensChi ρ p.1 := lensChi_pos_of_abs_lt_one hρ h1
  have halpha : 0 < lensAlpha 0 p.1 := by
    rw [lensAlpha_zero_fun]
    rw [abs_lt] at h1
    nlinarith [h1.1, h1.2]
  exact mul_pos (mul_pos hchi halpha) (lensZeta_pos h2 h3)

/-- `Δ₀` on the bottom edge of the lens is `A`. -/
private theorem regularDiscZero_of_snd_eq_zero {n : ℕ}
    {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {δ : ℝ}
    (hDbot : ∀ x, D (x, 0) = A x) {x y : ℝ} (hy : y = 0) :
    regularDiscZero D A B g δ (x, y) = A x := by
  subst hy
  exact regularDiscZero_bot hDbot x

/-- `Δ₀` on the arch of the lens is `B`. -/
private theorem regularDiscZero_of_snd_eq_arch {n : ℕ}
    {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {δ : ℝ}
    (hδ : 0 < δ) (hgval : ∀ x, arch x • g x = B x - A x) (hDtop : ∀ x, D (x, 1) = B x)
    {x y : ℝ} (hy : y = arch x) :
    regularDiscZero D A B g δ (x, y) = B x := by
  subst hy
  exact regularDiscZero_top hδ hgval hDtop x

theorem regularDiscZero_hbaseInj {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ)
    {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))} {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hDbot : ∀ x, D (x, 0) = A x) (hDtop : ∀ x, D (x, 1) = B x)
    (hgval : ∀ x, arch x • g x = B x - A x)
    (hinjA : Set.InjOn A (Set.Icc (-1 : ℝ) 1)) (hinjB : Set.InjOn B (Set.Icc (-1 : ℝ) 1))
    (hdisj : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, A x = B y → x = y ∧ x ^ 2 = 1) :
    ∀ p ∈ lens, ∀ q ∈ lens, p ≠ q →
      (∀ k : Fin 2 × Fin 2, lensBump ρ k p = lensBump ρ k q) →
      regularDiscZero D A B g δ p ≠ regularDiscZero D A B g δ q := by
  rintro ⟨px, py⟩ hp ⟨qx, qy⟩ hq hpq hbump hEq
  have hp' : |px| ≤ 1 ∧ 0 ≤ py ∧ py ≤ arch px := by simpa [lens] using hp
  have hq' : |qx| ≤ 1 ∧ 0 ≤ qy ∧ qy ≤ arch qx := by simpa [lens] using hq
  have hpx : px ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp hp'.1)
  have hqx : qx ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp hq'.1)
  by_cases hpint : (px, py) ∈ lensOpen
  · -- `p` is in the open lens: the bumps already separate the two points
    by_cases hqint : (qx, qy) ∈ lensOpen
    · exact hpq (lensBump_sep hρ hpint hqint hbump)
    · have hq0 : lensBump ρ ((0 : Fin 2), (0 : Fin 2)) (qx, qy) = 0 :=
        lensBump_eq_zero_of_not_mem_lensOpen hq hqint _
      have hp0 : 0 < lensBump ρ ((0 : Fin 2), (0 : Fin 2)) (px, py) :=
        lensBump_zero_zero_pos hρ hpint
      rw [hbump ((0 : Fin 2), (0 : Fin 2)), hq0] at hp0
      exact absurd hp0 (lt_irrefl 0)
  · -- both points avoid the open lens, hence lie on the two edges
    have hpb : py = 0 ∨ py = arch px := lens_snd_eq_zero_or_eq_arch hp hpint
    have hp0 : lensBump ρ ((0 : Fin 2), (0 : Fin 2)) (px, py) = 0 :=
      lensBump_eq_zero_of_not_mem_lensOpen hp hpint _
    have hq0 : lensBump ρ ((0 : Fin 2), (0 : Fin 2)) (qx, qy) = 0 := by
      rw [← hbump ((0 : Fin 2), (0 : Fin 2))]; exact hp0
    have hqint : (qx, qy) ∉ lensOpen := by
      intro h
      have hpos := lensBump_zero_zero_pos hρ h
      rw [hq0] at hpos
      exact absurd hpos (lt_irrefl 0)
    have hqb : qy = 0 ∨ qy = arch qx := lens_snd_eq_zero_or_eq_arch hq hqint
    rcases hpb with hp2 | hp2 <;> rcases hqb with hq2 | hq2
    · -- both on the bottom edge: `Δ₀ = A`
      have h1 : regularDiscZero D A B g δ (px, py) = A px :=
        regularDiscZero_of_snd_eq_zero hDbot hp2
      have h2 : regularDiscZero D A B g δ (qx, qy) = A qx :=
        regularDiscZero_of_snd_eq_zero hDbot hq2
      rw [h1, h2] at hEq
      exact hpq (Prod.ext (hinjA hpx hqx hEq) (by rw [hp2, hq2]))
    · -- `p` on the bottom edge, `q` on the arch: `A` meets `B` only at the cusps
      have h1 : regularDiscZero D A B g δ (px, py) = A px :=
        regularDiscZero_of_snd_eq_zero hDbot hp2
      have h2 : regularDiscZero D A B g δ (qx, qy) = B qx :=
        regularDiscZero_of_snd_eq_arch hδ hgval hDtop hq2
      rw [h1, h2] at hEq
      obtain ⟨hxy, hs⟩ := hdisj px hpx qx hqx hEq
      have har : arch qx = 0 := by simp only [arch]; rw [← hxy]; linarith
      exact hpq (Prod.ext hxy (by rw [hp2, hq2, har]))
    · -- `p` on the arch, `q` on the bottom edge (the symmetric case)
      have h1 : regularDiscZero D A B g δ (px, py) = B px :=
        regularDiscZero_of_snd_eq_arch hδ hgval hDtop hp2
      have h2 : regularDiscZero D A B g δ (qx, qy) = A qx :=
        regularDiscZero_of_snd_eq_zero hDbot hq2
      rw [h1, h2] at hEq
      obtain ⟨hxy, hs⟩ := hdisj qx hqx px hpx hEq.symm
      have har : arch px = 0 := by simp only [arch]; subst hxy; linarith
      exact hpq (Prod.ext hxy.symm (by rw [hp2, hq2]; exact har))
    · -- both on the arch: `Δ₀ = B`
      have h1 : regularDiscZero D A B g δ (px, py) = B px :=
        regularDiscZero_of_snd_eq_arch hδ hgval hDtop hp2
      have h2 : regularDiscZero D A B g δ (qx, qy) = B qx :=
        regularDiscZero_of_snd_eq_arch hδ hgval hDtop hq2
      rw [h1, h2] at hEq
      have hx : px = qx := hinjB hpx hqx hEq
      exact hpq (Prod.ext hx (by rw [hp2, hq2, hx]))

end Work.Drive.PushDisc
