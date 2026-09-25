import Mathlib
import Submission.NK.Reconstruct.gammaBaseChange
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.LevelInclExact.ellIncl_range_eq_ker_ellRestrict

namespace NK.Reconstruct.LevelInclExact

theorem ker_proj_le_range_gammaBaseChangeHom {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L : FrobLevel K K') :
    (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker ≤ (gammaBaseChangeHom ℓ L).range := by
  classical
  intro f hf
  rw [MonoidHom.mem_ker] at hf
  -- The set of elements of `Γ_L` satisfying one projection constraint per `K`-level containing `L`.
  let t : {N : FrobLevel K K' // L.L ≤ N.L} → Set (Gamma ↥L.L K' ℓ) := fun p =>
    {g | ellIncl ℓ L p.1 p.2
            (Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ) (levelExtend L p.1 p.2) g)
          = Gamma.proj (K := K) (K' := K') (ℓ := ℓ) p.1 f}
  have htclosed : ∀ p : {N : FrobLevel K K' // L.L ≤ N.L}, IsClosed (t p) := by
    intro p
    have hcont : Continuous fun g : Gamma ↥L.L K' ℓ =>
        ellIncl ℓ L p.1 p.2
          (Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ) (levelExtend L p.1 p.2) g) :=
      (continuous_of_discreteTopology (f := ellIncl ℓ L p.1 p.2)).comp
        (continuous_proj (K := ↥L.L) (K' := K') ℓ (levelExtend L p.1 p.2))
    exact isClosed_eq hcont continuous_const
  -- Finitely many constraints are satisfiable: pass to a common upper bound.
  have hFIP : ∀ u : Finset {N : FrobLevel K K' // L.L ≤ N.L}, (⋂ p ∈ u, t p).Nonempty := by
    intro u
    obtain ⟨T, hT, hLT⟩ := projSurj_finset_exists_upper_bound (K := K) (K' := K') L
      (u.image (fun p : {N : FrobLevel K K' // L.L ≤ N.L} => p.1))
    -- the projection of `f` to `T` lies in the kernel of the restriction to `L`
    have hker : Gamma.proj (K := K) (K' := K') (ℓ := ℓ) T f ∈ (ellRestrict ℓ L T hLT).ker := by
      rw [MonoidHom.mem_ker, Gamma.proj_compatible (K := K) (K' := K') L T hLT f, hf]
    -- hence, by exactness of the level inclusion, it is the image of a level-`L` element
    rw [← ellIncl_range_eq_ker_ellRestrict ℓ L T hLT, MonoidHom.mem_range] at hker
    obtain ⟨x, hx⟩ := hker
    -- which extends to an element of `Γ_L` by surjectivity of the projections
    obtain ⟨g, hg⟩ := proj_surjective (K := ↥L.L) (K' := K') ℓ (levelExtend L T hLT) x
    refine ⟨g, ?_⟩
    rw [Set.mem_iInter]
    intro p
    rw [Set.mem_iInter]
    intro hp
    have hpT : p.1.L ≤ T.L := hT p.1 (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    have hAB : (levelExtend L p.1 p.2).L ≤ (levelExtend L T hLT).L :=
      levelExtend_mono L p.1 T p.2 hLT hpT
    -- the value of `g` at the level `p.1` is the restriction of its value at `T`, which is `x`
    have h1 : Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ) (levelExtend L p.1 p.2) g
        = ellRestrict ℓ (levelExtend L p.1 p.2) (levelExtend L T hLT) hAB
            (Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ) (levelExtend L T hLT) g) :=
      (Gamma.proj_compatible (levelExtend L p.1 p.2) (levelExtend L T hLT) hAB g).symm
    -- the naturality square relates the inclusion at `T` and the inclusion at `p.1`
    have h2 : ellRestrict ℓ p.1 T hpT (ellIncl ℓ L T (p.2.trans hpT) x)
        = ellIncl ℓ L p.1 p.2
            (ellRestrict ℓ (levelExtend L p.1 p.2) (levelExtend L T (p.2.trans hpT))
              (levelExtend_mono L p.1 T p.2 (p.2.trans hpT) hpT) x) :=
      DFunLike.congr_fun (gammaBaseChange_ellIncl_comp ℓ L p.1 T p.2 hpT) x
    change ellIncl ℓ L p.1 p.2
        (Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ) (levelExtend L p.1 p.2) g)
      = Gamma.proj (K := K) (K' := K') (ℓ := ℓ) p.1 f
    rw [h1, hg, ← h2, hx, Gamma.proj_compatible (K := K) (K' := K') p.1 T hpT f]
  -- compactness upgrades finite satisfiability to the whole family
  have hne : (⋂ p : {N : FrobLevel K K' // L.L ≤ N.L}, t p).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hcon' : Set.univ ∩ ⋂ p, t p = ∅ := by rwa [Set.univ_inter]
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed t htclosed
      (Set.disjoint_iff_inter_eq_empty.mpr hcon')
    obtain ⟨g, hg⟩ := hFIP u
    have hmem : g ∈ Set.univ ∩ ⋂ p ∈ u, t p := ⟨trivial, hg⟩
    exact Set.disjoint_left.mp hu hmem.1 hmem.2
  obtain ⟨g, hg⟩ := hne
  rw [Set.mem_iInter] at hg
  rw [MonoidHom.mem_range]
  refine ⟨g, ?_⟩
  refine Gamma.ext (fun N => ?_)
  have hconstraint : ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
      (Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ)
        (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N)) g)
      = Gamma.proj (K := K) (K' := K') (ℓ := ℓ) (L.sup N) f :=
    hg ⟨L.sup N, FrobLevel.le_sup_left L N⟩
  rw [show Gamma.proj (K := K) (K' := K') (ℓ := ℓ) N (gammaBaseChangeHom ℓ L g)
      = ellRestrict ℓ N (L.sup N) (FrobLevel.le_sup_right L N)
          (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
            (Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ)
              (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N)) g)) from rfl,
    hconstraint]
  exact Gamma.proj_compatible (K := K) (K' := K') N (L.sup N) (FrobLevel.le_sup_right L N) f

end NK.Reconstruct.LevelInclExact
