import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Submodule

section General

variable {K : Type*} [Field K]
variable {M N O P : Type*}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup O] [Module K O] [AddCommGroup P] [Module K P]

/-- If `q ∘ s = id`, then `s ∘ q` agrees with the identity modulo `ker q`. -/
theorem comp_rightInverse_comp_eq (q : M →ₗ[K] O) (s : O →ₗ[K] M)
    (hs : q.comp s = LinearMap.id) (g : M →ₗ[K] N) (h1 : LinearMap.ker q ≤ LinearMap.ker g) :
    g.comp (s.comp q) = g := by
  ext x
  have hx : (s.comp q) x - x ∈ LinearMap.ker q := by
    rw [LinearMap.mem_ker]
    have hq : q ((s.comp q) x) = q x := by
      rw [show (s.comp q) x = s (q x) from rfl, ← LinearMap.comp_apply, hs,
        LinearMap.id_apply]
    rw [map_sub, hq, sub_self]
  have hg := h1 hx
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hg
  simpa only [LinearMap.comp_apply] using hg

/-- If `r ∘ i = id`, then `i ∘ r` agrees with the identity on `range i`. -/
theorem comp_leftInverse_comp_eq (i : P →ₗ[K] N) (r : N →ₗ[K] P)
    (hr : r.comp i = LinearMap.id) (g : M →ₗ[K] N) (h2 : LinearMap.range g ≤ LinearMap.range i) :
    i.comp (r.comp g) = g := by
  ext x
  obtain ⟨y, hy⟩ := h2 ⟨x, rfl⟩
  have hri : r (i y) = y := by rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
  show i (r (g x)) = g x
  rw [← hy, hri]

/-- A linear map `g` vanishing on `ker q` and with image in `range i` factors through
`q` and `i`. -/
theorem exists_comp_comp_eq (i : P →ₗ[K] N) (q : M →ₗ[K] O) (s : O →ₗ[K] M) (r : N →ₗ[K] P)
    (hs : q.comp s = LinearMap.id) (hr : r.comp i = LinearMap.id) (g : M →ₗ[K] N)
    (h1 : LinearMap.ker q ≤ LinearMap.ker g) (h2 : LinearMap.range g ≤ LinearMap.range i) :
    ∃ h : O →ₗ[K] P, i.comp (h.comp q) = g := by
  refine ⟨r.comp (g.comp s), ?_⟩
  have hA := comp_rightInverse_comp_eq q s hs g h1
  have hB := comp_leftInverse_comp_eq i r hr (g.comp (s.comp q))
    ((LinearMap.range_comp_le_range (s.comp q) g).trans h2)
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hB, hA]

/-- The map `g ↦ i ∘ g ∘ q` is injective when `i` is injective and `q` is surjective. -/
theorem comp_comp_injective {i : P →ₗ[K] N} (hi : Function.Injective i) {q : M →ₗ[K] O}
    (hq : Function.Surjective q) :
    Function.Injective (fun g : O →ₗ[K] P => i.comp (g.comp q)) := by
  intro g g' h
  ext y
  obtain ⟨x, rfl⟩ := hq y
  apply hi
  have := congrArg (fun f : M →ₗ[K] N => f x) h
  simpa only [LinearMap.comp_apply] using this

end General

theorem mul_mul_bijOn_hom_subtype {m n m' n' : ℕ}
    (V₁ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (W₁ : Submodule (ZMod 2) (Fin m → ZMod 2))
    (Q : Matrix (Fin n') (Fin n) (ZMod 2)) (ι : Matrix (Fin m) (Fin m') (ZMod 2))
    (hQ : LinearMap.ker Q.mulVecLin = V₁) (hQr : LinearMap.range Q.mulVecLin = ⊤)
    (hι : LinearMap.range ι.mulVecLin = W₁) (hιk : LinearMap.ker ι.mulVecLin = ⊥) :
    Set.BijOn (fun A : Matrix (Fin m') (Fin n') (ZMod 2) => ι * A * Q)
      Set.univ {B : Matrix (Fin m) (Fin n) (ZMod 2) |
        V₁ ≤ LinearMap.ker B.mulVecLin ∧ LinearMap.range B.mulVecLin ≤ W₁} := by
  have hq_surj : Function.Surjective Q.mulVecLin := LinearMap.range_eq_top.mp hQr
  have hi_inj : Function.Injective ι.mulVecLin := LinearMap.ker_eq_bot.mp hιk
  have hF : ∀ A : Matrix (Fin m') (Fin n') (ZMod 2),
      Matrix.toLin' (ι * A * Q)
        = (ι.mulVecLin).comp ((Matrix.toLin' A).comp (Q.mulVecLin)) := by
    intro A
    show (ι * A * Q).mulVecLin = (ι.mulVecLin).comp ((A.mulVecLin).comp (Q.mulVecLin))
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_assoc]
  refine ⟨?_, ?_, ?_⟩
  · intro A _
    constructor
    · change V₁ ≤ LinearMap.ker (Matrix.toLin' (ι * A * Q))
      rw [hF A, ← hQ]
      exact (LinearMap.ker_le_ker_comp Q.mulVecLin (Matrix.toLin' A)).trans
        (LinearMap.ker_le_ker_comp ((Matrix.toLin' A).comp Q.mulVecLin) ι.mulVecLin)
    · change LinearMap.range (Matrix.toLin' (ι * A * Q)) ≤ W₁
      rw [hF A]
      exact (LinearMap.range_comp_le_range ((Matrix.toLin' A).comp Q.mulVecLin)
        ι.mulVecLin).trans (le_of_eq hι)
  · intro A _ B _ hAB
    have hAB' : (ι.mulVecLin).comp ((Matrix.toLin' A).comp (Q.mulVecLin))
        = (ι.mulVecLin).comp ((Matrix.toLin' B).comp (Q.mulVecLin)) := by
      have := congrArg Matrix.toLin' hAB
      rwa [hF A, hF B] at this
    have hlin : Matrix.toLin' A = Matrix.toLin' B :=
      comp_comp_injective hi_inj hq_surj hAB'
    exact Matrix.toLin'.injective hlin
  · rintro B ⟨h1, h2⟩
    have h1' : LinearMap.ker Q.mulVecLin ≤ LinearMap.ker (Matrix.toLin' B) := hQ ▸ h1
    have h2' : LinearMap.range (Matrix.toLin' B) ≤ LinearMap.range ι.mulVecLin := hι ▸ h2
    obtain ⟨s, hs⟩ := Q.mulVecLin.exists_rightInverse_of_surjective hQr
    obtain ⟨r, hr⟩ := ι.mulVecLin.exists_leftInverse_of_injective hιk
    obtain ⟨g, hg⟩ := exists_comp_comp_eq ι.mulVecLin Q.mulVecLin s r hs hr
      (Matrix.toLin' B) h1' h2'
    refine ⟨LinearMap.toMatrix' g, Set.mem_univ _, ?_⟩
    apply Matrix.toLin'.injective
    rw [hF (LinearMap.toMatrix' g), Matrix.toLin'_toMatrix']
    exact hg

end Commons.LinearAlgebra.Submodule