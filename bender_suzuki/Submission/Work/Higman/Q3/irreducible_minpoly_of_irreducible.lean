import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- **Irreducibility of the minimal polynomial of an "irreducible" endomorphism.**

Let `V` be a finite, non-trivial `𝔽₂`-vector space and `a : V →ₗ[𝔽₂] V` an endomorphism
whose only `a`-invariant subspaces are `⊥` and `⊤` (i.e. `V` is a simple module over the
subalgebra `𝔽₂[a]`). Then the minimal polynomial of `a` is irreducible.

The proof is by contradiction: a factorisation `minpoly = f * g` with `f, g` monic and of
positive degree yields, in the endomorphism ring, `aeval a f * aeval a g = 0` with both
factors nonzero. Hence `ker (aeval a f)` is a nonzero, proper `a`-invariant subspace,
contradicting the hypothesis. -/
theorem irreducible_minpoly_of_irreducible
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (a : V →ₗ[ZMod 2] V)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ v ∈ U, a v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Irreducible (minpoly (ZMod 2) a) := by
  classical
  have hfin : Module.Finite (ZMod 2) V := inferInstance
  have hint : IsIntegral (ZMod 2) a := IsIntegral.of_finite (ZMod 2) a
  have hmonic : (minpoly (ZMod 2) a).Monic := minpoly.monic hint
  rw [Polynomial.Monic.irreducible_iff_natDegree hmonic]
  refine ⟨minpoly.ne_one (ZMod 2) a, ?_⟩
  intro f g hf hg hfg
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfdeg, hgdeg⟩ := hcon
  have hfne : f ≠ 0 := hf.ne_zero
  have hgne : g ≠ 0 := hg.ne_zero
  have hdeg : (minpoly (ZMod 2) a).natDegree = f.natDegree + g.natDegree := by
    rw [← hfg, hf.natDegree_mul hg]
  have hflt : f.natDegree < (minpoly (ZMod 2) a).natDegree := by
    rw [hdeg]; omega
  -- The two factors do not kill `a`.
  have hfaeval : Polynomial.aeval a f ≠ 0 := by
    intro hzero
    have hdvd : minpoly (ZMod 2) a ∣ f := minpoly.dvd_iff.mpr hzero
    have hle := Polynomial.natDegree_le_of_dvd hdvd hfne
    omega
  have hgaeval : Polynomial.aeval a g ≠ 0 := by
    intro hzero
    have hdvd : minpoly (ZMod 2) a ∣ g := minpoly.dvd_iff.mpr hzero
    have hle := Polynomial.natDegree_le_of_dvd hdvd hgne
    omega
  -- Their product is zero (it is `aeval a (minpoly a)`).
  have hprod : Polynomial.aeval a f * Polynomial.aeval a g = 0 := by
    rw [← Polynomial.aeval_mul, hfg]
    exact minpoly.aeval (ZMod 2) a
  -- `aeval a f` commutes with `a`, being a polynomial in `a`.
  have hcomm : Polynomial.aeval a f * a = a * Polynomial.aeval a f := by
    have h1 : Polynomial.aeval a (f * (Polynomial.X : Polynomial (ZMod 2))) =
              Polynomial.aeval a ((Polynomial.X : Polynomial (ZMod 2)) * f) := by
      rw [mul_comm]
    rw [Polynomial.aeval_mul, Polynomial.aeval_mul] at h1
    rw [Polynomial.aeval_X] at h1
    exact h1
  -- `ker (aeval a f)` is a nonzero, proper, `a`-invariant subspace.
  have hker_bot : LinearMap.ker (Polynomial.aeval a f) ≠ ⊥ := by
    intro hk
    have hinj : Function.Injective (Polynomial.aeval a f) := LinearMap.ker_eq_bot.mp hk
    have hgz : Polynomial.aeval a g = 0 := by
      ext v
      apply hinj
      have hp := congrArg (fun e : Module.End (ZMod 2) V => e v) hprod
      rw [Module.End.mul_apply] at hp
      simpa using hp
    exact hgaeval hgz
  have hker_top : LinearMap.ker (Polynomial.aeval a f) ≠ ⊤ := by
    intro hk
    have hz : Polynomial.aeval a f = 0 := by
      ext v
      have hv : v ∈ LinearMap.ker (Polynomial.aeval a f) := by rw [hk]; exact Submodule.mem_top
      exact LinearMap.mem_ker.mp hv
    exact hfaeval hz
  have hinv : ∀ v ∈ LinearMap.ker (Polynomial.aeval a f),
      a v ∈ LinearMap.ker (Polynomial.aeval a f) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hcv : (Polynomial.aeval a f * a) v = (a * Polynomial.aeval a f) v := by rw [hcomm]
    rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_zero] at hcv
    exact hcv
  rcases hirr (LinearMap.ker (Polynomial.aeval a f)) hinv with h | h
  · exact hker_bot h
  · exact hker_top h

end Work.Higman.Q3
