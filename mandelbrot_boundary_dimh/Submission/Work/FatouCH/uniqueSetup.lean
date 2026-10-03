import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Fatou uniqueness: the `ℤ`-equivariant extension `ψ` of `Φ ∘ Φ₀⁻¹`

Preparatory definitions and lemmas for `Work.FatouCH.fatouUnique_of_existsOrbit`.

Let `Q` be a set, `Φ₀ : ℂ → ℂ` injective on `Q` and surjective modulo `ℤ` (`FatouRepExists`),
and `Φ : ℂ → ℂ` a second map whose fibres modulo `ℤ` relative to `Φ₀` are the same — the
*transfer* hypothesis `htrans`, which in the application is Shishikura's orbit relation
`MandelDim.FatouOrbit` (§A.2.1).  Define

`psiOf Q Φ₀ Φ hex u = Φ z + n`  where `u = Φ₀ z + n`, `z ∈ Q`, `n : ℤ`,

using a choice of representative `(z,n)` of `u` (which exists by `hex`).  Then

* `psiOf_apply_rep`: the value does not depend on the chosen representative (well-definedness),
* `psiOf_injective`: `ψ` is injective,
* `psiOf_add_one`: `ψ (u + 1) = ψ u + 1`,
* `psiOf_eq_id_add_const_of_affine`: if `ψ` is affine with slope `a`, the `+1`-equivariance
  forces `a = 1`, so `ψ u = u + b`.
-/

namespace Work.FatouCH

open Set Metric Complex
open scoped Topology

noncomputable section

/-- `MandelDim.Qreg b₁ b₂` is open (the intersection of at most two pairs of open half planes). -/
theorem qreg_isOpen (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h1 : ∀ a : ℂ, IsOpen {z : ℂ | -|(z - a).im| < (z - a).re} := fun a =>
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : ∀ b : ℂ, IsOpen {z : ℂ | (z - b).re < |(z - b).im|} := fun b =>
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · rw [show MandelDim.Qreg (none : Option ℂ) none = univ by
        ext z; simp [MandelDim.Qreg]]
      exact isOpen_univ
    · rw [show MandelDim.Qreg (none : Option ℂ) (some b) = {z : ℂ | (z - b).re < |(z - b).im|} by
        ext z; simp [MandelDim.Qreg]]
      exact h2 b
  · rcases b₂ with _ | b
    · rw [show MandelDim.Qreg (some a) (none : Option ℂ) = {z : ℂ | -|(z - a).im| < (z - a).re} by
        ext z; simp [MandelDim.Qreg]]
      exact h1 a
    · rw [show MandelDim.Qreg (some a) (some b) =
          {z : ℂ | -|(z - a).im| < (z - a).re} ∩ {z : ℂ | (z - b).re < |(z - b).im|} by
        ext z; simp [MandelDim.Qreg]]
      exact (h1 a).inter (h2 b)

/-- `Φ₀` hits every complex number modulo `ℤ`: `∀ u, ∃ z ∈ Q, ∃ n : ℤ, Φ₀ z + n = u`.
This is the surjectivity half of `MandelDim.FatouExists`. -/
def FatouRepExists (Q : Set ℂ) (Φ₀ : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, ∃ p : ℂ × ℤ, p.1 ∈ Q ∧ Φ₀ p.1 + (p.2 : ℂ) = u

variable {Q : Set ℂ} {Φ₀ Φ : ℂ → ℂ}

/-- The chosen representative of `u` as `Φ₀ z + n` (first component `z`, second `n`). -/
def psiRep (hex : FatouRepExists Q Φ₀) (u : ℂ) : ℂ × ℤ := Classical.choose (hex u)

theorem psiRep_fst_mem (hex : FatouRepExists Q Φ₀) (u : ℂ) : (psiRep hex u).1 ∈ Q :=
  (Classical.choose_spec (hex u)).1

theorem psiRep_spec (hex : FatouRepExists Q Φ₀) (u : ℂ) :
    Φ₀ (psiRep hex u).1 + ((psiRep hex u).2 : ℂ) = u :=
  (Classical.choose_spec (hex u)).2

/-- The `ℤ`-equivariant function `ψ` extending `Φ ∘ Φ₀⁻¹` to all of `ℂ`. -/
def psiOf (Q : Set ℂ) (Φ₀ Φ : ℂ → ℂ) (hex : FatouRepExists Q Φ₀) (u : ℂ) : ℂ :=
  Φ (psiRep hex u).1 + ((psiRep hex u).2 : ℂ)

/-- Integer cast arithmetic helper. -/
theorem intCast_sub (m n : ℤ) : ((m - n : ℤ) : ℂ) = (m : ℂ) - (n : ℂ) := by
  push_cast; ring

/-- **Well-definedness of `ψ`.**  For any representative `u = Φ₀ z + n` (`z ∈ Q`, `n : ℤ`),
`ψ u = Φ z + n`. -/
theorem psiOf_apply_rep (hex : FatouRepExists Q Φ₀)
    (htrans : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℤ, Φ₀ z' = Φ₀ z + (k : ℂ) → Φ z' = Φ z + (k : ℂ))
    {z u : ℂ} (hz : z ∈ Q) (n : ℤ) (h : Φ₀ z + (n : ℂ) = u) :
    psiOf Q Φ₀ Φ hex u = Φ z + (n : ℂ) := by
  have hz₀ : (psiRep hex u).1 ∈ Q := psiRep_fst_mem hex u
  have hspec : Φ₀ (psiRep hex u).1 + ((psiRep hex u).2 : ℂ) = u := psiRep_spec hex u
  have h1 : Φ₀ (psiRep hex u).1 + ((psiRep hex u).2 : ℂ) = Φ₀ z + (n : ℂ) := by
    rw [hspec, h]
  have hrel : Φ₀ (psiRep hex u).1 = Φ₀ z + (((n - (psiRep hex u).2 : ℤ)) : ℂ) := by
    rw [intCast_sub]
    linear_combination h1
  have hΦ := htrans z hz (psiRep hex u).1 hz₀ (n - (psiRep hex u).2) hrel
  show Φ (psiRep hex u).1 + ((psiRep hex u).2 : ℂ) = Φ z + (n : ℂ)
  rw [hΦ, intCast_sub]
  ring

/-- **Injectivity of `ψ`**, from the transfer relation in both directions. -/
theorem psiOf_injective (hex : FatouRepExists Q Φ₀)
    (htrans : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℤ,
      (Φ₀ z' = Φ₀ z + (k : ℂ) ↔ Φ z' = Φ z + (k : ℂ))) :
    Function.Injective (psiOf Q Φ₀ Φ hex) := by
  intro u₁ u₂ huv
  have hz₁ : (psiRep hex u₁).1 ∈ Q := psiRep_fst_mem hex u₁
  have hz₂ : (psiRep hex u₂).1 ∈ Q := psiRep_fst_mem hex u₂
  have hsp₁ : Φ₀ (psiRep hex u₁).1 + ((psiRep hex u₁).2 : ℂ) = u₁ := psiRep_spec hex u₁
  have hsp₂ : Φ₀ (psiRep hex u₂).1 + ((psiRep hex u₂).2 : ℂ) = u₂ := psiRep_spec hex u₂
  have huv' : Φ (psiRep hex u₁).1 + ((psiRep hex u₁).2 : ℂ)
      = Φ (psiRep hex u₂).1 + ((psiRep hex u₂).2 : ℂ) := huv
  have hΦ : Φ (psiRep hex u₁).1
      = Φ (psiRep hex u₂).1 + ((((psiRep hex u₂).2 - (psiRep hex u₁).2 : ℤ)) : ℂ) := by
    rw [intCast_sub]
    linear_combination huv'
  have hΦ₀ : Φ₀ (psiRep hex u₁).1
      = Φ₀ (psiRep hex u₂).1 + ((((psiRep hex u₂).2 - (psiRep hex u₁).2 : ℤ)) : ℂ) :=
    (htrans (psiRep hex u₂).1 hz₂ (psiRep hex u₁).1 hz₁ _).mpr hΦ
  rw [← hsp₁, ← hsp₂, hΦ₀, intCast_sub]
  ring

/-- `ψ` is `1`-periodic up to the shift: `ψ (u + 1) = ψ u + 1`. -/
theorem psiOf_add_one (hex : FatouRepExists Q Φ₀)
    (htrans : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℤ, Φ₀ z' = Φ₀ z + (k : ℂ) → Φ z' = Φ z + (k : ℂ))
    (u : ℂ) : psiOf Q Φ₀ Φ hex (u + 1) = psiOf Q Φ₀ Φ hex u + 1 := by
  have hz : (psiRep hex u).1 ∈ Q := psiRep_fst_mem hex u
  have hspec : Φ₀ (psiRep hex u).1 + ((psiRep hex u).2 : ℂ) = u := psiRep_spec hex u
  have hrep : Φ₀ (psiRep hex u).1 + (((psiRep hex u).2 + 1 : ℤ) : ℂ) = u + 1 := by
    have hcast : (((psiRep hex u).2 + 1 : ℤ) : ℂ) = ((psiRep hex u).2 : ℂ) + 1 := by
      push_cast; ring
    rw [hcast, ← add_assoc]
    exact congrArg (· + 1) hspec
  have h1 : psiOf Q Φ₀ Φ hex (u + 1)
      = Φ (psiRep hex u).1 + (((psiRep hex u).2 + 1 : ℤ) : ℂ) :=
    psiOf_apply_rep hex htrans hz ((psiRep hex u).2 + 1) hrep
  have h2 : psiOf Q Φ₀ Φ hex u
      = Φ (psiRep hex u).1 + ((psiRep hex u).2 : ℂ) :=
    psiOf_apply_rep hex htrans hz ((psiRep hex u).2) hspec
  rw [h1, h2]
  have hcast : (((psiRep hex u).2 + 1 : ℤ) : ℂ) = ((psiRep hex u).2 : ℂ) + 1 := by
    push_cast; ring
  rw [hcast]
  ring

/-- If an affine map is `+1`-equivariant, its slope is `1`. -/
theorem psiOf_eq_id_add_const_of_affine {ψ : ℂ → ℂ} {a b : ℂ}
    (hlin : ∀ u, ψ u = a * u + b) (hper : ∀ u, ψ (u + 1) = ψ u + 1) :
    a = 1 ∧ ∀ u, ψ u = u + b := by
  have h0 : a * (0 + 1) + b = a * 0 + b + 1 := by
    rw [← hlin (0 + 1), ← hlin 0]
    exact hper 0
  have ha : a = 1 := by
    linear_combination h0
  refine ⟨ha, fun u => ?_⟩
  rw [hlin u, ha]
  ring

end

end Work.FatouCH
