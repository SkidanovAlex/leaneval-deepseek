import Mathlib
import Submission.Work.KT.ExtGen.Basic
import Submission.Work.KT.ExtGen.Triple
import Submission.Work.KT.ExtGen.tripleIncl_injective
import Submission.Work.KT.k0_basic

/-!
# `Work.KT.ExtGen.ext_nesting` — associativity of the external product

The two ways of multiplying the three reduced classes `s`, `t`, `u` agree, up to the canonical
algebra isomorphism `pairAssocEquiv`.

The proof compares the two sides in the common target `tripleAlg V W Z = C(S^a × S^b × S^c)`
(see `Submission/Work/KT/ExtGen/Triple.lean`): both are the product of the three pulled-back
classes in `K₀` of that algebra (using the four `IsExtProd` hypotheses, the naturality of the
`K₀`-product from `k0_basic`, and the commutation lemmas of the comparison maps), and the
comparison map `Kpair (V × (W × Z)) → tripleAlg V W Z` is injective on reduced classes
(`Work.KT.ExtGen.tripleIncl_injective`, the Künneth input).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Work.KT

namespace ExtGen

noncomputable section

set_option synthInstance.maxHeartbeats 800000

/-! ## `K₀`-valued helpers (extracted from `k0_basic`) -/

lemma mapA_comp_gen {A B C : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Ring C]
    [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) :=
  k0_basic.2.2.1 A B C φ.toRingHom ψ.toRingHom

lemma mapA_comp_apply_gen {A B C : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    [Ring C] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) (x : K0 A) :
    K0.mapA (ψ.comp φ) x = K0.mapA ψ (K0.mapA φ x) := by
  rw [mapA_comp_gen φ ψ, AddMonoidHom.comp_apply]

lemma mapA_mul_gen {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (hAcomm : ∀ x y : A, x * y = y * x) (φ : A →ₐ[ℂ] B)
    (μA : K0 A →+ K0 A →+ K0 A) (μB : K0 B →+ K0 B →+ K0 B)
    (hA : IsK0Mul μA) (hB : IsK0Mul μB) (x y : K0 A) :
    K0.mapA φ (μA x y) = μB (K0.mapA φ x) (K0.mapA φ y) :=
  k0_basic.2.1 A B hAcomm φ.toRingHom μA μB hA hB x y

/-- ROUTE (node `ext_generator`, its dependency): associativity of the external product.

Both sides are the product of the three pulled-back classes in `K(S^a × S^b × S^c)`, so they agree. -/
theorem ext_nesting (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0Z : Ball Z) (hZ : y0Z ∈ bdry Z)
    (y0VW : Ball (V × W)) (hVW : y0VW ∈ bdry (V × W))
    (y0WZ : Ball (W × Z)) (hWZ : y0WZ ∈ bdry (W × Z))
    (y0VWZ : Ball (V × (W × Z))) (hVWZ : y0VWZ ∈ bdry (V × (W × Z)))
    (y0VWZ' : Ball ((V × W) × Z)) (hVWZ' : y0VWZ' ∈ bdry ((V × W) × Z))
    (μ12 : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (h12 : IsExtProd V W y0V y0W y0VW μ12)
    (μ23 : K0 (Kpair W) →+ K0 (Kpair Z) →+ K0 (Kpair (W × Z)))
    (h23 : IsExtProd W Z y0W y0Z y0WZ μ23)
    (μ1_23 : K0 (Kpair V) →+ K0 (Kpair (W × Z)) →+ K0 (Kpair (V × (W × Z))))
    (h1_23 : IsExtProd V (W × Z) y0V y0WZ y0VWZ μ1_23)
    (μ12_3 : K0 (Kpair (V × W)) →+ K0 (Kpair Z) →+ K0 (Kpair ((V × W) × Z)))
    (h12_3 : IsExtProd (V × W) Z y0VW y0Z y0VWZ' μ12_3)
    (s : K0 (Kpair V)) (hs : K0.mapA (augPair V y0V) s = 0)
    (t : K0 (Kpair W)) (ht : K0.mapA (augPair W y0W) t = 0)
    (u : K0 (Kpair Z)) (hu : K0.mapA (augPair Z y0Z) u = 0) :
    K0.mapA (pairAssocEquiv V W Z).toAlgHom (μ12_3 (μ12 s t) u) = μ1_23 s (μ23 t u) := by
  -- the multiplications of `K₀` on the algebras involved
  obtain ⟨μT, hμT, -, hassocT, -⟩ :=
    k0_basic.1 (tripleAlg V W Z) (fun x y => Subtype.ext (mul_comm x.1 y.1))
  obtain ⟨μP, hμP, -, -, -⟩ :=
    k0_basic.1 (prodAlg V (W × Z)) (fun x y => Subtype.ext (mul_comm x.1 y.1))
  obtain ⟨μQ, hμQ, -, -, -⟩ :=
    k0_basic.1 (prodAlg (V × W) Z) (fun x y => Subtype.ext (mul_comm x.1 y.1))
  obtain ⟨μPW, hμPW, -, -, -⟩ :=
    k0_basic.1 (prodAlg V W) (fun x y => Subtype.ext (mul_comm x.1 y.1))
  obtain ⟨μWZ, hμWZ, -, -, -⟩ :=
    k0_basic.1 (prodAlg W Z) (fun x y => Subtype.ext (mul_comm x.1 y.1))
  -- reducedness and the smash characterisation of the four hypotheses
  have hred12 : K0.mapA (augPair (V × W) y0VW) (μ12 s t) = 0 := (h12 s t hs ht).1
  have hsm12 := (h12 s t hs ht).2
  have hred23 : K0.mapA (augPair (W × Z) y0WZ) (μ23 t u) = 0 := (h23 t u ht hu).1
  have hsm23 := (h23 t u ht hu).2
  have hsm1_23 := (h1_23 s (μ23 t u) hs hred23).2
  have hsm12_3 := (h12_3 (μ12 s t) u hred12 hu).2
  -- the product of the pulled-back classes for the pair `(V, W)`
  have hVW : K0.mapA (triplePullVW V W Z) (μ12 s t)
      = μT (K0.mapA (triplePullV V W Z) s) (K0.mapA (triplePullW V W Z) t) := by
    calc K0.mapA (triplePullVW V W Z) (μ12 s t)
        = K0.mapA (tripleInclPW V W Z) (K0.mapA (smashIncl V W) (μ12 s t)) := by
          rw [← tripleInclPW_comp_smashIncl,
              mapA_comp_apply_gen (smashIncl V W) (tripleInclPW V W Z) (μ12 s t)]
      _ = K0.mapA (tripleInclPW V W Z)
            (μPW (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t)) := by
          rw [hsm12 μPW hμPW]
      _ = μT (K0.mapA (tripleInclPW V W Z) (K0.mapA (pullFst V W) s))
            (K0.mapA (tripleInclPW V W Z) (K0.mapA (pullSnd V W) t)) :=
          mapA_mul_gen (fun x y : prodAlg V W => Subtype.ext (mul_comm x.1 y.1))
            (tripleInclPW V W Z) μPW μT hμPW hμT _ _
      _ = μT (K0.mapA (triplePullV V W Z) s) (K0.mapA (triplePullW V W Z) t) := by
          rw [← mapA_comp_apply_gen (pullFst V W) (tripleInclPW V W Z) s,
              tripleInclPW_comp_pullFst,
              ← mapA_comp_apply_gen (pullSnd V W) (tripleInclPW V W Z) t,
              tripleInclPW_comp_pullSnd]
  -- the product of the pulled-back classes for the pair `(W, Z)`
  have hWZ : K0.mapA (triplePullWZ V W Z) (μ23 t u)
      = μT (K0.mapA (triplePullW V W Z) t) (K0.mapA (triplePullZ V W Z) u) := by
    calc K0.mapA (triplePullWZ V W Z) (μ23 t u)
        = K0.mapA (tripleInclWZ V W Z) (K0.mapA (smashIncl W Z) (μ23 t u)) := by
          rw [← tripleInclWZ_comp_smashIncl,
              mapA_comp_apply_gen (smashIncl W Z) (tripleInclWZ V W Z) (μ23 t u)]
      _ = K0.mapA (tripleInclWZ V W Z)
            (μWZ (K0.mapA (pullFst W Z) t) (K0.mapA (pullSnd W Z) u)) := by
          rw [hsm23 μWZ hμWZ]
      _ = μT (K0.mapA (tripleInclWZ V W Z) (K0.mapA (pullFst W Z) t))
            (K0.mapA (tripleInclWZ V W Z) (K0.mapA (pullSnd W Z) u)) :=
          mapA_mul_gen (fun x y : prodAlg W Z => Subtype.ext (mul_comm x.1 y.1))
            (tripleInclWZ V W Z) μWZ μT hμWZ hμT _ _
      _ = μT (K0.mapA (triplePullW V W Z) t) (K0.mapA (triplePullZ V W Z) u) := by
          rw [← mapA_comp_apply_gen (pullFst W Z) (tripleInclWZ V W Z) t,
              tripleInclWZ_comp_pullFst,
              ← mapA_comp_apply_gen (pullSnd W Z) (tripleInclWZ V W Z) u,
              tripleInclWZ_comp_pullSnd]
  -- the left-hand side in the triple algebra
  have hL : K0.mapA (tripleIncl V W Z)
        (K0.mapA (pairAssocEquiv V W Z).toAlgHom (μ12_3 (μ12 s t) u))
      = μT (μT (K0.mapA (triplePullV V W Z) s) (K0.mapA (triplePullW V W Z) t))
          (K0.mapA (triplePullZ V W Z) u) := by
    calc K0.mapA (tripleIncl V W Z)
          (K0.mapA (pairAssocEquiv V W Z).toAlgHom (μ12_3 (μ12 s t) u))
        = K0.mapA ((tripleIncl V W Z).comp (pairAssocEquiv V W Z).toAlgHom)
            (μ12_3 (μ12 s t) u) := by
          rw [← mapA_comp_apply_gen (pairAssocEquiv V W Z).toAlgHom (tripleIncl V W Z)
            (μ12_3 (μ12 s t) u)]
      _ = K0.mapA (tripleIncl' V W Z) (μ12_3 (μ12 s t) u) := by
          rw [← tripleIncl'_eq_comp_pairAssoc]
      _ = K0.mapA (tripleInclQ V W Z)
            (K0.mapA (smashIncl (V × W) Z) (μ12_3 (μ12 s t) u)) := by
          rw [← tripleInclQ_comp_smashIncl,
              mapA_comp_apply_gen (smashIncl (V × W) Z) (tripleInclQ V W Z) (μ12_3 (μ12 s t) u)]
      _ = K0.mapA (tripleInclQ V W Z)
            (μQ (K0.mapA (pullFst (V × W) Z) (μ12 s t)) (K0.mapA (pullSnd (V × W) Z) u)) := by
          rw [hsm12_3 μQ hμQ]
      _ = μT (K0.mapA (tripleInclQ V W Z) (K0.mapA (pullFst (V × W) Z) (μ12 s t)))
            (K0.mapA (tripleInclQ V W Z) (K0.mapA (pullSnd (V × W) Z) u)) :=
          mapA_mul_gen (fun x y : prodAlg (V × W) Z => Subtype.ext (mul_comm x.1 y.1))
            (tripleInclQ V W Z) μQ μT hμQ hμT _ _
      _ = μT (K0.mapA (triplePullVW V W Z) (μ12 s t)) (K0.mapA (triplePullZ V W Z) u) := by
          rw [← mapA_comp_apply_gen (pullFst (V × W) Z) (tripleInclQ V W Z) (μ12 s t),
              tripleInclQ_comp_pullFst,
              ← mapA_comp_apply_gen (pullSnd (V × W) Z) (tripleInclQ V W Z) u,
              tripleInclQ_comp_pullSnd]
      _ = μT (μT (K0.mapA (triplePullV V W Z) s) (K0.mapA (triplePullW V W Z) t))
            (K0.mapA (triplePullZ V W Z) u) := by
          rw [hVW]
  -- the right-hand side in the triple algebra
  have hR : K0.mapA (tripleIncl V W Z) (μ1_23 s (μ23 t u))
      = μT (K0.mapA (triplePullV V W Z) s)
          (μT (K0.mapA (triplePullW V W Z) t) (K0.mapA (triplePullZ V W Z) u)) := by
    calc K0.mapA (tripleIncl V W Z) (μ1_23 s (μ23 t u))
        = K0.mapA (tripleInclP V W Z)
            (K0.mapA (smashIncl V (W × Z)) (μ1_23 s (μ23 t u))) := by
          rw [← tripleInclP_comp_smashIncl,
              mapA_comp_apply_gen (smashIncl V (W × Z)) (tripleInclP V W Z) (μ1_23 s (μ23 t u))]
      _ = K0.mapA (tripleInclP V W Z)
            (μP (K0.mapA (pullFst V (W × Z)) s)
              (K0.mapA (pullSnd V (W × Z)) (μ23 t u))) := by
          rw [hsm1_23 μP hμP]
      _ = μT (K0.mapA (tripleInclP V W Z) (K0.mapA (pullFst V (W × Z)) s))
            (K0.mapA (tripleInclP V W Z) (K0.mapA (pullSnd V (W × Z)) (μ23 t u))) :=
          mapA_mul_gen (fun x y : prodAlg V (W × Z) => Subtype.ext (mul_comm x.1 y.1))
            (tripleInclP V W Z) μP μT hμP hμT _ _
      _ = μT (K0.mapA (triplePullV V W Z) s)
            (K0.mapA (triplePullWZ V W Z) (μ23 t u)) := by
          rw [← mapA_comp_apply_gen (pullFst V (W × Z)) (tripleInclP V W Z) s,
              tripleInclP_comp_pullFst,
              ← mapA_comp_apply_gen (pullSnd V (W × Z)) (tripleInclP V W Z) (μ23 t u),
              tripleInclP_comp_pullSnd]
      _ = μT (K0.mapA (triplePullV V W Z) s)
            (μT (K0.mapA (triplePullW V W Z) t) (K0.mapA (triplePullZ V W Z) u)) := by
          rw [hWZ]
  -- the difference is killed by the comparison map and is reduced
  have hzero : K0.mapA (tripleIncl V W Z)
      (K0.mapA (pairAssocEquiv V W Z).toAlgHom (μ12_3 (μ12 s t) u) - μ1_23 s (μ23 t u))
      = 0 := by
    rw [map_sub, hL, hR, hassocT]
    exact sub_self _
  have hredL : K0.mapA (augPair (V × (W × Z)) y0VWZ)
      (K0.mapA (pairAssocEquiv V W Z).toAlgHom (μ12_3 (μ12 s t) u)) = 0 := by
    rw [← mapA_comp_apply_gen (pairAssocEquiv V W Z).toAlgHom (augPair (V × (W × Z)) y0VWZ)
        (μ12_3 (μ12 s t) u),
      augPair_comp_pairAssocEquiv V W Z y0VWZ,
      mapA_augPair_apply_eq_of_mem_bdry ((V × W) × Z) (ballAssoc V W Z y0VWZ) y0VWZ'
        ((bdry_ballAssoc_iff V W Z y0VWZ).mpr hVWZ) hVWZ']
    exact (h12_3 (μ12 s t) u hred12 hu).1
  have hredR : K0.mapA (augPair (V × (W × Z)) y0VWZ) (μ1_23 s (μ23 t u)) = 0 :=
    (h1_23 s (μ23 t u) hs hred23).1
  have hfin := tripleIncl_injective V W Z y0VWZ hVWZ
    (K0.mapA (pairAssocEquiv V W Z).toAlgHom (μ12_3 (μ12 s t) u) - μ1_23 s (μ23 t u))
    (by rw [map_sub, hredL, hredR, sub_self]) hzero
  exact sub_eq_zero.mp hfin

end

end ExtGen

end Work.KT
