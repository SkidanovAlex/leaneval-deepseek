import Mathlib
import Submission.Work.ORHomAlg.Map

namespace Work.ORHomAlg.Flat

universe u

/-- **The pullback ("3×3") map of an injective map along a surjection.**
Let `g : N →ₗ[R] N'` be injective and `π' : P →ₗ[R] N'` surjective (in the application `π'` is a
projective cover).  Put `g' := Submodule.mkQ (LinearMap.range g) : N' →ₗ[R] N' ⧸ range g`,
`π_C := g'.comp π' : P →ₗ[R] C` (surjective) and `Q := LinearMap.ker π_C`.
Then there is a surjective linear map `σ : Q →ₗ[R] N` with `g.comp σ = π'.comp Q.subtype` and
`σ q = 0 ↔ (q : P) ∈ LinearMap.ker π'`.

Construction: `Q = {p : P | π' p ∈ LinearMap.range g}` since `ker g' = range g`.  Let
`ρ : Q →ₗ[R] LinearMap.range g` be `LinearMap.codRestrict (LinearMap.range g) (π'.comp Q.subtype)`
(this is well defined by the description of `Q`), and let
`e : N ≃ₗ[R] LinearMap.range g := LinearEquiv.ofInjective g hg` (so `↑(e x) = g x` by
`LinearEquiv.ofInjective_apply`).  Then take `σ := e.symm.toLinearMap.comp ρ`.  The three
properties follow by unwinding (`g (σ q) = ↑(e (σ q)) = ↑(ρ q) = π' q`; surjectivity: given `n`,
pick `p` with `π' p = g n` using `hπ'`, then `p ∈ Q` because `g' (g n) = 0` and `ker g' = range g`,
and `σ ⟨p, _⟩ = n` since `g` is injective; the kernel is computed from `g.comp σ = π'.comp
Q.subtype` and injectivity of `g`). -/
theorem exists_sigma_of_injective {R : Type u} [Ring R] {N : Type u} [AddCommGroup N] [Module R N]
    {N' : Type u} [AddCommGroup N'] [Module R N'] {P : Type u} [AddCommGroup P] [Module R P]
    (g : N →ₗ[R] N') (hg : Function.Injective g) (π' : P →ₗ[R] N') (hπ' : Function.Surjective π') :
    ∃ σ : (LinearMap.ker ((Submodule.mkQ (LinearMap.range g)).comp π')) →ₗ[R] N,
      g.comp σ = π'.comp (LinearMap.ker ((Submodule.mkQ (LinearMap.range g)).comp π')).subtype ∧
      Function.Surjective σ ∧
      (∀ q, σ q = 0 ↔ (q : P) ∈ LinearMap.ker π') := by
  classical
  set g' : N' →ₗ[R] N' ⧸ LinearMap.range g := Submodule.mkQ (LinearMap.range g) with hg'def
  set Q : Submodule R P := LinearMap.ker (g'.comp π') with hQdef
  have mem_Q : ∀ p : P, p ∈ Q ↔ g' (π' p) = 0 := fun p => by
    rw [hQdef, LinearMap.mem_ker, LinearMap.comp_apply]
  have range_eq : ∀ y : N', y ∈ LinearMap.range g ↔ g' y = 0 := by
    intro y
    rw [hg'def, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range g)).symm
  have hρ_well : ∀ q : Q, (π'.comp Q.subtype) q ∈ LinearMap.range g := by
    intro q
    rw [range_eq, LinearMap.comp_apply, Submodule.subtype_apply]
    exact (mem_Q (q : P)).1 q.2
  set ρ : Q →ₗ[R] LinearMap.range g :=
    LinearMap.codRestrict (LinearMap.range g) (π'.comp Q.subtype) hρ_well with hρdef
  set e : N ≃ₗ[R] LinearMap.range g := LinearEquiv.ofInjective g hg with hedef
  have hcoe : ∀ x : N, ((e x : LinearMap.range g) : N') = g x := by
    intro x; rw [hedef]; exact LinearEquiv.ofInjective_apply g (h := hg) x
  set σ : Q →ₗ[R] N := (e.symm).toLinearMap.comp ρ with hσdef
  have h1 : g.comp σ = π'.comp Q.subtype := by
    ext q
    have hρq : (ρ q : N') = π' (q : P) := by
      rw [hρdef, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    have heq : ((e (e.symm (ρ q)) : LinearMap.range g)) = ρ q := e.apply_symm_apply (ρ q)
    calc g (σ q) = g (e.symm (ρ q)) := by rw [hσdef]; rfl
      _ = ((e (e.symm (ρ q))) : N') := (hcoe (e.symm (ρ q))).symm
      _ = (ρ q : N') := by rw [heq]
      _ = π' (q : P) := hρq
      _ = (π'.comp Q.subtype) q := by rw [LinearMap.comp_apply, Submodule.subtype_apply]
  refine ⟨σ, h1, ?_, ?_⟩
  · intro n
    obtain ⟨p, hp⟩ := hπ' (g n)
    have hpQ : p ∈ Q := (mem_Q p).2 (by rw [hp]; exact (range_eq (g n)).1 ⟨n, rfl⟩)
    refine ⟨⟨p, hpQ⟩, ?_⟩
    apply hg
    have hx := LinearMap.congr_fun h1 ⟨p, hpQ⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hx
    rw [hx, hp]
  · intro q
    have key : g (σ q) = π' (q : P) := by
      have hx := LinearMap.congr_fun h1 q
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hx
      exact hx
    rw [← hg.eq_iff (a := σ q) (b := 0), map_zero, key, LinearMap.mem_ker]


end Work.ORHomAlg.Flat
