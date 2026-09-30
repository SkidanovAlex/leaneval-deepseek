import Mathlib
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.mulEq
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Compatibility of the product of the assembled spectral sequence with the page product

`mssMul` is the product on the bidegree-indexed pages `mssE 𝕜 W r (s,q) = pEraw 𝕜 W r s (s+q)`
of the multiplicative Serre spectral sequence of a filtered cochain complex with a product
(`Submission/Work/Pi6/MSS/AssembleCore.lean`).  `mssNorm` is the identification of that page with
the concrete page `pEraw 𝕜 W r s (s+q)`.

Both `mssMul` and `mssNorm` are built out of transports (`pCast`) of the concrete product
`pd_mul` along equalities of the (filtration degree, cohomological degree) indices
(`EI a = a.1`, `EN a = a.1 + a.2`).  The lemmas below are the bookkeeping facts about these
transports: they only depend on the two endpoints of the transport
(`pCast_congr`, a consequence of proof irrelevance), they compose
(`pCast_comp_apply`), the transport is the underlying linear map of the isomorphism `pEcast`
(`pEcast_hom_apply`), and `pd_mul` is natural with respect to them
(`pd_mul_pCast_apply`).  With these, the compatibility of `mssMul` with `D.mul` reduces to the
identification `D.mul = pd_mul` of the page data (`Work.Pi6.MSS.mulEq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

/-- A transport `pCast` along *reflexive* index equalities is the identity. -/
lemma pCast_self_apply (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) {s n : ℕ}
    (h : s = s) (h' : n = n) (x : pEraw 𝕜 W r s n) : pCast 𝕜 W r h h' x = x := by
  rw [Subsingleton.elim h rfl, Subsingleton.elim h' rfl]
  exact pCast_apply_self 𝕜 W r x

/-- The transport `pCast` only depends on the endpoints of the index equalities. -/
lemma pCast_congr (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) {s s' n n' : ℕ}
    (h1 h2 : s = s') (h1' h2' : n = n') : pCast 𝕜 W r h1 h1' = pCast 𝕜 W r h2 h2' := by
  rw [Subsingleton.elim h1 h2, Subsingleton.elim h1' h2']

/-- Transports of pages along index equalities compose. -/
lemma pCast_comp_apply (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) {s s' s'' n n' n'' : ℕ}
    (h1 : s = s') (h2 : s' = s'') (h1' : n = n') (h2' : n' = n'') (x : pEraw 𝕜 W r s n) :
    pCast 𝕜 W r h2 h2' (pCast 𝕜 W r h1 h1' x) = pCast 𝕜 W r (h1.trans h2) (h1'.trans h2') x := by
  cases h1
  cases h2
  cases h1'
  cases h2'
  simp only [pCast_apply_self]

/-- The concrete product `pd_mul` is natural with respect to the transports of the pages. -/
lemma pd_mul_pCast_apply (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ)
    (sa na sb nb Sa Na Sb Nb : ℕ) (h1 : sa = Sa) (h2 : na = Na) (h3 : sb = Sb) (h4 : nb = Nb)
    (H : sa + sb = Sa + Sb) (H' : na + nb = Na + Nb)
    (x : pEraw 𝕜 W r sa na) (y : pEraw 𝕜 W r sb nb) :
    pCast 𝕜 W r H H' (pd_mul r sa na sb nb x y)
      = pd_mul r Sa Na Sb Nb (pCast 𝕜 W r h1 h2 x) (pCast 𝕜 W r h3 h4 y) := by
  cases h1
  cases h2
  cases h3
  cases h4
  simp only [pCast_self_apply]

/-- The underlying linear map of the transport isomorphism `pEcast` is `pCast`. -/
lemma pEcast_hom_apply (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) {s s' n n' : ℕ}
    (h : s = s') (h' : n = n') (x : pEraw 𝕜 W r s n) :
    (pEcast 𝕜 W r h h').hom x = pCast 𝕜 W r h h' x := by
  cases h
  cases h'
  rw [pEcast_hom_id, pCast_apply_self]
  exact ConcreteCategory.id_apply x

/-- The normalization `mssNorm` of a page is the transport `pCast` of the index equalities. -/
lemma mssNorm_hom_apply (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s q : ℕ)
    (x : mssE 𝕜 W r ((s : ℤ), (q : ℤ))) :
    (mssNorm 𝕜 W r s q).hom x = pCast 𝕜 W r (EI_pair s q) (EN_pair s q) x := by
  rw [mssNorm]
  exact pEcast_hom_apply 𝕜 W r _ _ x

/-- The product of the bidegree-indexed pages, on the honest part of the bidegree range, is the
transport of the concrete product `pd_mul`. -/
lemma mssMul_apply_pos (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) {a b c : ℤ × ℤ}
    (ha : Enn a) (hb : Enn b) (h : a + b = c)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMul 𝕜 W r a b c h x y
      = pCast 𝕜 W r (congrArg EI h) (congrArg EN h)
          (pCast 𝕜 W r (EI_add ha hb) (EN_add ha hb)
            (pd_mul r (EI a) (EN a) (EI b) (EN b) x y)) := by
  rw [mssMul_pos 𝕜 W r ha hb h]
  simp only [mssCast_eq_pCast, mssMulStep, LinearMap.comp_apply, LinearMap.llcomp_apply]

theorem mssMulCompat (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜)
    (D : Work.Pi6.MSS.PagesData 𝕜 W) (r s q s' q' : ℕ) (hr : 2 ≤ r)
    (x : Work.Pi6.MSS.mssE 𝕜 W r ((s : ℤ), (q : ℤ)))
    (y : Work.Pi6.MSS.mssE 𝕜 W r ((s' : ℤ), (q' : ℤ))) :
    (Work.Pi6.MSS.mssNorm 𝕜 W r (s + s') (q + q')).hom
        (Work.Pi6.MSS.mssMul 𝕜 W r ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
          (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp) x y)
      = (Work.Pi6.MSS.pEcast 𝕜 W r (rfl : s + s' = s + s') (by omega)).hom
        (D.mul r s (s + q) s' (s' + q') ((Work.Pi6.MSS.mssNorm 𝕜 W r s q).hom x)
          ((Work.Pi6.MSS.mssNorm 𝕜 W r s' q').hom y)) := by
  have ha : Enn ((s : ℤ), (q : ℤ)) := Enn_pair s q
  have hb : Enn ((s' : ℤ), (q' : ℤ)) := Enn_pair s' q'
  have hc : ((s : ℤ), (q : ℤ)) + ((s' : ℤ), (q' : ℤ))
      = (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) := by ext <;> simp
  -- the composite index equalities of the assembled cast
  have HE : EI ((s : ℤ), (q : ℤ)) + EI ((s' : ℤ), (q' : ℤ)) = s + s' :=
    (EI_add ha hb).trans ((congrArg EI hc).trans (EI_pair (s + s') (q + q')))
  have KE : EN ((s : ℤ), (q : ℤ)) + EN ((s' : ℤ), (q' : ℤ)) = (s + s') + (q + q') :=
    (EN_add ha hb).trans ((congrArg EN hc).trans (EN_pair (s + s') (q + q')))
  -- the same transport, with the total degree of the normalized product
  have K2 : EN ((s : ℤ), (q : ℤ)) + EN ((s' : ℤ), (q' : ℤ)) = (s + q) + (s' + q') :=
    KE.trans (by omega : (s + s') + (q + q') = (s + q) + (s' + q'))
  have hN : (s + q) + (s' + q') = (s + s') + (q + q') := by omega
  -- naturality of `pd_mul` with respect to the normalization
  have hnat := pd_mul_pCast_apply 𝕜 W r (EI ((s : ℤ), (q : ℤ))) (EN ((s : ℤ), (q : ℤ)))
    (EI ((s' : ℤ), (q' : ℤ))) (EN ((s' : ℤ), (q' : ℤ))) s (s + q) s' (s' + q')
    (EI_pair s q) (EN_pair s q) (EI_pair s' q') (EN_pair s' q') HE K2 x y
  -- (1) unfold `mssNorm` and `mssMul` and merge the three transports of the left hand side
  have e1 : (mssNorm 𝕜 W r (s + s') (q + q')).hom
        (mssMul 𝕜 W r ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
          (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp) x y)
      = pCast 𝕜 W r HE KE
          (pd_mul r (EI ((s : ℤ), (q : ℤ))) (EN ((s : ℤ), (q : ℤ)))
            (EI ((s' : ℤ), (q' : ℤ))) (EN ((s' : ℤ), (q' : ℤ))) x y) := by
    rw [mssNorm_hom_apply, mssMul_apply_pos 𝕜 W r ha hb hc]
    rw [pCast_comp_apply, pCast_comp_apply]
  -- (2) rewrite the unnormalized product as the transport of the normalized one
  have e2 : pCast 𝕜 W r HE KE
        (pd_mul r (EI ((s : ℤ), (q : ℤ))) (EN ((s : ℤ), (q : ℤ)))
          (EI ((s' : ℤ), (q' : ℤ))) (EN ((s' : ℤ), (q' : ℤ))) x y)
      = pCast 𝕜 W r (rfl : s + s' = s + s') hN
          (pd_mul r s (s + q) s' (s' + q') (pCast 𝕜 W r (EI_pair s q) (EN_pair s q) x)
            (pCast 𝕜 W r (EI_pair s' q') (EN_pair s' q') y)) := by
    rw [← pCast_congr 𝕜 W r (HE.trans rfl) HE (K2.trans hN) KE]
    rw [← pCast_comp_apply 𝕜 W r HE rfl K2 hN
      (pd_mul r (EI ((s : ℤ), (q : ℤ))) (EN ((s : ℤ), (q : ℤ)))
        (EI ((s' : ℤ), (q' : ℤ))) (EN ((s' : ℤ), (q' : ℤ))) x y)]
    rw [hnat]
  -- (3) identify the page product with the one of the page data
  have e3 : pCast 𝕜 W r (rfl : s + s' = s + s') hN
        (pd_mul r s (s + q) s' (s' + q') (pCast 𝕜 W r (EI_pair s q) (EN_pair s q) x)
          (pCast 𝕜 W r (EI_pair s' q') (EN_pair s' q') y))
      = (pEcast 𝕜 W r (rfl : s + s' = s + s') (by omega)).hom
        (D.mul r s (s + q) s' (s' + q') ((mssNorm 𝕜 W r s q).hom x)
          ((mssNorm 𝕜 W r s' q').hom y)) := by
    rw [pEcast_hom_apply, mulEq 𝕜 W D r s (s + q) s' (s' + q'), mssNorm_hom_apply,
      mssNorm_hom_apply]
  exact e1.trans (e2.trans e3)

end Work.Pi6.MSS
