import Mathlib
import Submission.Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks
import Submission.Work.Coherence.NormIrr
import Submission.Work.CharCore.Coherence
import Submission.Work.Coherence.cross_core
import Submission.Work.Coherence.cfInner_expand_zsmul
import Submission.Work.Coherence.isometryOnAll_extend

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The two-coherent-blocks argument for *virtual* (not necessarily irreducible) images

`Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks` proves the orthogonality
`⟨σ x, ρ y⟩ = 0` (`x ∈ X`, `y ∈ Y`) under the hypothesis that each image `σ x` is, after
multiplication by a *uniform* sign `δ` (with `δ * δ = 1`), an **irreducible** character of `G`
(and likewise `ε • ρ y ∈ Irr G`).

Here we remove that hypothesis: it suffices that the images `σ x`, `ρ y` be **virtual**
characters (`Work.CharCore.IsVChar`).  An isometry of `ℤ[X]` which happens to send `x ∈ X` to a
virtual character must send it to `±` an irreducible character, because
`⟨σ x, σ x⟩ = ⟨x, x⟩ = 1` and a virtual character of norm one is `±χ` with `χ` irreducible
(`Work.Coherence.isometry_image_irr`, `Work.Coherence.vchar_norm_one`).

What is *not* immediate is that the sign is the *same* for all `x ∈ X`.  This is where the
degree-zero part of the lattice and the common isometry `τ` enter: for `x, x' ∈ X` with degrees
`n = x 1`, `n' = x' 1`, the element `n' • x - n • x' ∈ ℤ[X]⁰ ⊆ ℤ[S]⁰` is mapped by `σ` to
`τ (n' • x - n • x')`, which has degree `0`; hence
`n' * (σ x 1) = n * (σ x' 1)`.  Since `σ x = s χ` and `σ x' = s' χ'` with `s, s' ∈ {1, -1}` and
`χ, χ'` of positive degree, a sign mismatch would make the two sides of that equation have
opposite signs, so `s = s'`.  This is `uniform_sign_of_isometry_vchar`, and it is exactly the
uniform sign hypotheses `hδ`, `hε` of the irreducible version.

## Main results

* `sign_eq_of_deg_eq` — sign rigidity from the degree equation (arithmetic core).
* `deg_sub_mul_apply_one` — the degree equation `n' * (σ x 1) = n * (σ x' 1)` produced by `τ`.
* `isometry_vchar_image_signed` — an isometric image of `x ∈ X` which is virtual is `±Irr`.
* `uniform_sign_of_isometry_vchar` — the sign can be chosen uniformly on `X`.
* `cfInner_eq_zero_of_two_coherent_blocks_vchar` — the two blocks are orthogonal.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

/-! ### The arithmetic core: a sign is determined by a degree equation -/

/-- **Sign rigidity from a degree equation.**  If `s, s' ∈ {1, -1}` and
`d' * (s * n) = d * (s' * n')` with all of `d, d', n, n'` positive natural numbers — so that all
four cast factors are strictly positive real numbers — then `s = s'`.  A sign mismatch would make
the two sides of the equation have opposite signs. -/
theorem sign_eq_of_deg_eq {d d' n n' : ℕ} (hd : 0 < d) (hd' : 0 < d') (hn : 0 < n)
    (hn' : 0 < n') {s s' : ℂ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1)
    (h : (d' : ℂ) * (s * (n : ℂ)) = (d : ℂ) * (s' * (n' : ℂ))) : s = s' := by
  rcases hs with h1 | h1 <;> rcases hs' with h2 | h2
  · rw [h1, h2]
  · exfalso
    rw [h1, h2] at h
    have h2' : ((d' * n + d * n' : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination h
    exact (Nat.cast_ne_zero.mpr (by positivity : d' * n + d * n' ≠ 0)) h2'
  · exfalso
    rw [h1, h2] at h
    have h2' : ((d' * n + d * n' : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination -h
    exact (Nat.cast_ne_zero.mpr (by positivity : d' * n + d * n' ≠ 0)) h2'
  · rw [h1, h2]

/-! ### The degree equation produced by the common isometry `τ` -/

/-- **The degree of `σ` at `x` and `x'` is balanced.**  If `x, x' ∈ X ⊆ S`, `n = x 1`, `n' = x' 1`,
and `σ` agrees with `τ` on `ℤ[X]⁰` while `τ` kills degrees on `ℤ[S]⁰`, then
`n' * (σ x 1) = n * (σ x' 1)`.

Indeed `n' • x - n • x' ∈ ℤ[X]⁰` (its value at `1` is `n' * n - n * n' = 0`) and hence in `ℤ[S]⁰`,
so `σ (n' • x - n • x') = τ (n' • x - n • x')` has degree `0`; expanding `σ` over the `ℤ`-linear
combination gives exactly the claim. -/
theorem deg_sub_mul_apply_one {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S X : Finset (H → ℂ)} {τ σ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hXS : X ⊆ S) (hτV : ∀ α ∈ ZSpan0 S, τ α 1 = 0)
    (hσ0 : ∀ α ∈ ZSpan0 X, σ α = τ α)
    {x x' : H → ℂ} (hx : x ∈ X) (hx' : x' ∈ X) {n n' : ℕ}
    (hn : x 1 = (n : ℂ)) (hn' : x' 1 = (n' : ℂ)) :
    (n' : ℂ) * (σ x 1) - (n : ℂ) * (σ x' 1) = 0 := by
  have hu0 : (n' : ℤ) • x - (n : ℤ) • x' ∈ ZSpan0 X :=
    zsmul_deg_sub_mem_zSpan0 hx hx' hn hn'
  have huS : (n' : ℤ) • x - (n : ℤ) • x' ∈ ZSpan0 S := zSpan0_mono hXS hu0
  have hzero : σ ((n' : ℤ) • x - (n : ℤ) • x') 1 = 0 := by
    rw [hσ0 _ hu0, hτV _ huS]
  have h4 : σ ((n' : ℤ) • x - (n : ℤ) • x') 1
      = (n' : ℂ) * (σ x 1) - (n : ℂ) * (σ x' 1) := by
    rw [map_sub, map_zsmul, map_zsmul]
    simp [zsmul_eq_mul]
  rw [h4] at hzero
  exact hzero

/-! ### Signed irreducibility of an isometric image -/

/-- **An isometric image which is virtual is `±Irr`.**  If `X` is orthonormal, `σ` is an isometry
of `ℤ[X]`, `x ∈ X` and `σ x` is a virtual character of `G`, then there is a sign `s ∈ {1, -1}`
with `s • σ x` an irreducible character of `G` (in the `Work.CharCore.Irr G` vocabulary).

This is `isometry_image_irr` (norm preservation together with `vchar_norm_one`) transported
through the `Work.CharCore`/`Work.Coherence` dictionary. -/
theorem isometry_vchar_image_signed {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {X : Finset (H → ℂ)} {σ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hXo : Orthonormal X) (hσ : IsometryOnAll X σ)
    {x : H → ℂ} (hx : x ∈ X) (hv : Work.CharCore.IsVChar (σ x)) :
    ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ s • σ x ∈ Work.CharCore.Irr G := by
  obtain ⟨χ, hχIrr, hχ⟩ :=
    isometry_image_irr hXo hσ hx ((Work.CharCore.IsVChar_iff_coherence (σ x)).mp hv)
  rcases hχ with h | h
  · exact ⟨1, Or.inl rfl, by
      rw [one_smul, h]
      exact (Work.CharCore.mem_Irr_iff_coherence).mpr hχIrr⟩
  · exact ⟨-1, Or.inr rfl, by
      rw [neg_one_smul, h, neg_neg]
      exact (Work.CharCore.mem_Irr_iff_coherence).mpr hχIrr⟩

/-! ### The sign is uniform on the block -/

/-- **Uniform sign on a coherent block.**  Let `X ⊆ S` be a finite set of irreducible characters
of `H`, `τ` an isometry on `ℤ[S]⁰` which kills degrees on `ℤ[S]⁰`, and `σ` a `ℤ`-linear isometry
on all of `ℤ[X]` which agrees with `τ` on `ℤ[X]⁰`.  If every image `σ x` (`x ∈ X`) is a virtual
character of `G` and `X` has at least two elements, then there is a single sign `δ` with
`δ * δ = 1` and `δ • σ x ∈ Irr G` for **all** `x ∈ X`.

The two hypotheses at the start of the proof are structural: `X ⊆ Irr H` makes `X` orthonormal,
so `isometry_vchar_image_signed` applies to each element; the degree argument of
`deg_sub_mul_apply_one` then shows that the individual signs, matched against the degree of the
image, cannot differ on two distinct elements of `X`. -/
theorem uniform_sign_of_isometry_vchar {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S X : Finset (H → ℂ)} {τ σ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hXS : X ⊆ S) (hIrr : ∀ x ∈ S, x ∈ Work.CharCore.Irr H)
    (hτV : ∀ α ∈ ZSpan0 S, τ α 1 = 0)
    (hσ0 : ∀ α ∈ ZSpan0 X, σ α = τ α) (hσ : IsometryOnAll X σ)
    (hσV : ∀ x ∈ X, Work.CharCore.IsVChar (σ x)) (hcardX : 2 ≤ X.card) :
    ∃ δ : ℂ, δ * δ = 1 ∧ ∀ x ∈ X, δ • σ x ∈ Work.CharCore.Irr G := by
  classical
  have hXsub : X ⊆ Work.CharCore.Irr H := fun x hx => hIrr x (hXS hx)
  have hXo : Orthonormal X := Work.CharCore.Orthonormal_Irr.mono hXsub
  have hsign : ∀ x ∈ X, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ s • σ x ∈ Work.CharCore.Irr G :=
    fun x hx => isometry_vchar_image_signed hXo hσ hx (hσV x hx)
  obtain ⟨x₀, hx₀X⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  obtain ⟨s₀, hs₀1, hs₀2⟩ := hsign x₀ hx₀X
  refine ⟨s₀, ?_, ?_⟩
  · rcases hs₀1 with h | h <;> rw [h] <;> norm_num
  · intro x hx
    by_cases hx0 : x = x₀
    · rw [hx0]
      exact hs₀2
    · -- the sign at `x` and at `x₀` agree, by the degree equation
      obtain ⟨sx, hsx1, hsx2⟩ := hsign x hx
      obtain ⟨na, hna, hx₀1⟩ :=
        Work.Coherence.irr_degree_pos ((Work.CharCore.mem_Irr_iff_coherence).mp (hXsub hx₀X))
      obtain ⟨nb, hnb, hx1⟩ :=
        Work.Coherence.irr_degree_pos ((Work.CharCore.mem_Irr_iff_coherence).mp (hXsub hx))
      obtain ⟨n₀, hn₀, hχ₀1⟩ :=
        Work.Coherence.irr_degree_pos ((Work.CharCore.mem_Irr_iff_coherence).mp hs₀2)
      obtain ⟨nx, hnx, hχx1⟩ :=
        Work.Coherence.irr_degree_pos ((Work.CharCore.mem_Irr_iff_coherence).mp hsx2)
      have hs₀sq : s₀ * s₀ = 1 := by rcases hs₀1 with h | h <;> rw [h] <;> norm_num
      have hsxsq : sx * sx = 1 := by rcases hsx1 with h | h <;> rw [h] <;> norm_num
      -- the degree of `σ x₀` (resp. `σ x`) is the sign times the degree of the irreducible
      have hσx₀1 : σ x₀ 1 = s₀ * (n₀ : ℂ) := by
        have hsmul : (s₀ • σ x₀) 1 = s₀ * (σ x₀ 1) := by simp
        rw [hsmul] at hχ₀1
        calc σ x₀ 1 = (s₀ * s₀) * (σ x₀ 1) := by rw [hs₀sq, one_mul]
          _ = s₀ * (s₀ * (σ x₀ 1)) := by ring
          _ = s₀ * (n₀ : ℂ) := by rw [hχ₀1]
      have hσx1 : σ x 1 = sx * (nx : ℂ) := by
        have hsmul : (sx • σ x) 1 = sx * (σ x 1) := by simp
        rw [hsmul] at hχx1
        calc σ x 1 = (sx * sx) * (σ x 1) := by rw [hsxsq, one_mul]
          _ = sx * (sx * (σ x 1)) := by ring
          _ = sx * (nx : ℂ) := by rw [hχx1]
      -- the degree equation of `τ`
      have hEq : (nb : ℂ) * (σ x₀ 1) - (na : ℂ) * (σ x 1) = 0 :=
        deg_sub_mul_apply_one (S := S) (X := X) (τ := τ) (σ := σ) (x := x₀) (x' := x)
          (n := na) (n' := nb) hXS hτV hσ0 hx₀X hx hx₀1 hx1
      have hmain : (nb : ℂ) * (s₀ * (n₀ : ℂ)) = (na : ℂ) * (sx * (nx : ℂ)) := by
        have h' : (nb : ℂ) * (σ x₀ 1) = (na : ℂ) * (σ x 1) := sub_eq_zero.mp hEq
        rw [hσx₀1, hσx1] at h'
        exact h'
      have hs0sx : s₀ = sx := sign_eq_of_deg_eq (d := na) (d' := nb) (n := n₀) (n' := nx)
        hna hnb hn₀ hnx hs₀1 hsx1 hmain
      rw [hs0sx]
      exact hsx2

/-- **The two-coherent-blocks theorem for virtual images.**  In the situation of
`Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks` it is enough that the images of the two
disjoint blocks `X`, `Y` under the isometries `σ`, `ρ` be *virtual* characters: the two blocks are
then orthogonal, `⟨σ x, ρ y⟩ = 0`.

The proof derives, for each of the two blocks, the uniform sign `δ` (resp. `ε`) supplied by
`uniform_sign_of_isometry_vchar` and then invokes the irreducible version of the theorem. -/
theorem cfInner_eq_zero_of_two_coherent_blocks_vchar {H G : Type*} [Group H] [Fintype H]
    [Group G] [Fintype G] {S X Y : Finset (H → ℂ)} {τ σ ρ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hXY : Disjoint X Y) (hsub : X ∪ Y ⊆ S)
    (hIrr : ∀ x ∈ S, x ∈ Work.CharCore.Irr H) (hτ : Work.Coherence.IsometryOn S τ)
    (hτV : ∀ α ∈ Work.Coherence.ZSpan0 S, τ α 1 = 0)
    (hσ0 : ∀ α ∈ Work.Coherence.ZSpan0 X, σ α = τ α)
    (hσ : Work.Coherence.IsometryOnAll X σ)
    (hσV : ∀ x ∈ X, Work.CharCore.IsVChar (σ x))
    (hρ0 : ∀ α ∈ Work.Coherence.ZSpan0 Y, ρ α = τ α)
    (hρ : Work.Coherence.IsometryOnAll Y ρ) (hρV : ∀ y ∈ Y, Work.CharCore.IsVChar (ρ y))
    (hcardX : 2 ≤ X.card) (hcardY : 2 ≤ Y.card) :
    ∀ x ∈ X, ∀ y ∈ Y, Work.Coherence.cfInner (σ x) (ρ y) = 0 := by
  have hXS : X ⊆ S := fun z hz => hsub (Finset.mem_union_left Y hz)
  have hYS : Y ⊆ S := fun z hz => hsub (Finset.mem_union_right X hz)
  exact cfInner_eq_zero_of_two_coherent_blocks hXY hsub hIrr hτ hτV hσ0 hσ
    (uniform_sign_of_isometry_vchar hXS hIrr hτV hσ0 hσ hσV hcardX)
    hρ0 hρ (uniform_sign_of_isometry_vchar hYS hIrr hτV hρ0 hρ hρV hcardY)
    hcardX hcardY

end Work.Coherence
