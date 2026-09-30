import Mathlib
import Submission.Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap
import Submission.Work.Pi6.SRANGE.homQuot_bridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Surjectivity on `H_q` implies surjectivity on cycles modulo boundaries

The concrete model `Z_q ⧸ B_q` of the homology of a chain complex of `ℤ`-modules is naturally
equivalent to `H_q` (`Work.Pi6.SRANGE.homQuotEquiv`), and
`Work.Pi6.SRANGE.homQuotEquiv_naturality` says that, under these equivalences,
`HomologicalComplex.homologyMap f q` is exactly the concrete map `Work.Pi6.SRANGE.homQuotMap ℤ f q`.
Since the equivalences are bijections, surjectivity of the former gives surjectivity of the latter,
and unrolling the latter gives the elementwise statement: every cycle `w` of `D` is, modulo a
boundary `v` of `D`, the image `cycMap f q w'` of a cycle `w'` of `C`.

The instance `AddCommGroup.toIntModule` competes with the canonical `Submodule.module` structure on
`↥(Z_q)`; the concrete models of the SRANGE chapter are elaborated with the latter, so we lower the
priority of the former to keep the two consistent.
-/

attribute [local instance 10] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Work.Pi6.SRANGE

namespace Work.Pi6.SQ

theorem h2OfHomologySurjective {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) (q : ℕ)
    (hsurj : Function.Surjective (HomologicalComplex.homologyMap f q).hom) :
    ∀ w : ↥(Work.Pi6.SRANGE.Cyc D q),
      ∃ w' : ↥(Work.Pi6.SRANGE.Cyc C q), ∃ v : ↥(Work.Pi6.SRANGE.Bdry D q),
        Work.Pi6.SRANGE.cycMap f q w' + Work.Pi6.SRANGE.mum D q v = w := by
  -- Surjectivity of the concrete map `Z_q ⧸ B_q → Z'_q ⧸ B'_q`.
  have hsurjQ : Function.Surjective (homQuotMap ℤ f q) := by
    intro y
    obtain ⟨a, ha⟩ := hsurj (homQuotEquiv D q y)
    refine ⟨(homQuotEquiv C q).symm a, ?_⟩
    apply (homQuotEquiv D q).injective
    have h := homQuotEquiv_naturality f q ((homQuotEquiv C q).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h, ha]
  -- The class of a cycle is carried to the class of its image.
  have hmap : ∀ x : ↥(Cyc C q),
      homQuotMap ℤ f q (Submodule.Quotient.mk x) = Submodule.Quotient.mk (cycMap f q x) := by
    intro x
    rw [homQuotMap_mk]
    rfl
  intro w
  obtain ⟨y, hy⟩ := hsurjQ (Submodule.Quotient.mk w)
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  have h1 : (Submodule.Quotient.mk (cycMap f q x) : homQuot ℤ D q) = Submodule.Quotient.mk w :=
    (hmap x).symm.trans hy
  -- `cycMap f q x - w` is a boundary of `D`.
  have h2 : cycMap f q x - w ∈ BcOf D q := by
    rw [← quo_mk_eq_zero_iff D q (cycMap f q x - w)]
    have hq : (Submodule.mkQ ((LinearMap.range (D.d (q+1) q).hom).comap (Cyc D q).subtype))
        (cycMap f q x - w) = 0 := by
      rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, h1, sub_self]
    exact hq
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (by rwa [← mum_range D q] at h2)
  exact ⟨x, -v, by rw [map_neg, hv]; abel⟩

end Work.Pi6.SQ
