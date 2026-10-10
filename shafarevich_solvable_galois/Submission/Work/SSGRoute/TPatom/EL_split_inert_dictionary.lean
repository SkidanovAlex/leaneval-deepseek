import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Work.SSGRoute.Sha2Lib.exists_unramified_inert_cyclic_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TPatom

open scoped NumberField Pointwise

section Helpers

variable {k K1 K1L E EL : Type} [Field k] [NumberField k] [Field K1] [NumberField K1]
  [Field K1L] [NumberField K1L] [Field E] [NumberField E] [Field EL] [NumberField EL]
  [Algebra k K1] [Algebra k K1L] [Algebra K1 E] [Algebra K1L EL]
  [Algebra k E] [Algebra k EL] [IsScalarTower k K1 E] [IsScalarTower k K1L EL]

/-- **Compatibility of the transport of rings of integers.**

If `eK1 : K₁ ≅ K₁L` and `eEL : E ≅ EL` are `k`-algebra isomorphisms such that
`eEL (a • x) = eK1 a • eEL x` for all `a ∈ K₁`, `x ∈ E`, then the induced maps on rings of
integers are compatible with the algebra maps: `fE (algebraMap a) = algebraMap (f1 a)`. -/
theorem mapAlgEquiv_compat (eK1 : K1 ≃ₐ[k] K1L) (eEL : E ≃ₐ[k] EL)
    (hcompat : ∀ (a : K1) (x : E), eEL (a • x) = eK1 a • eEL x) (a : 𝓞 K1) :
    (NumberField.RingOfIntegers.mapAlgEquiv eEL) (algebraMap (𝓞 K1) (𝓞 E) a)
      = algebraMap (𝓞 K1L) (𝓞 EL) (NumberField.RingOfIntegers.mapAlgEquiv eK1 a) := by
  apply Subtype.ext
  change eEL (algebraMap K1 E (a : K1)) = algebraMap K1L EL (eK1 (a : K1))
  calc eEL (algebraMap K1 E (a : K1))
      = eEL ((a : K1) • (1 : E)) := by simp only [Algebra.algebraMap_eq_smul_one]
    _ = eK1 (a : K1) • eEL 1 := hcompat (a : K1) 1
    _ = eK1 (a : K1) • 1 := by simp only [map_one]
    _ = algebraMap K1L EL (eK1 (a : K1)) := by simp only [Algebra.algebraMap_eq_smul_one]

/-- **Transport of the `LiesOver` relation along a compatible pair of `k`-algebra isomorphisms.**

If `𝔮'` lies over `p'` in the image world, then the pulled back prime `𝔮 = 𝔮'.comap fE` lies over
`u = p'.comap f1` in the source world. -/
theorem liesOver_comap_transport (eK1 : K1 ≃ₐ[k] K1L) (eEL : E ≃ₐ[k] EL)
    (hcompat : ∀ (a : K1) (x : E), eEL (a • x) = eK1 a • eEL x)
    (p' : IsDedekindDomain.HeightOneSpectrum (𝓞 K1L))
    (𝔮' : IsDedekindDomain.HeightOneSpectrum (𝓞 EL))
    (h : 𝔮'.asIdeal.LiesOver p'.asIdeal) :
    (Ideal.comap (NumberField.RingOfIntegers.mapAlgEquiv eEL : 𝓞 E →+* 𝓞 EL)
        𝔮'.asIdeal).LiesOver
      (Ideal.comap (NumberField.RingOfIntegers.mapAlgEquiv eK1 : 𝓞 K1 →+* 𝓞 K1L)
        p'.asIdeal) := by
  refine ⟨?_⟩
  have hcomp : (NumberField.RingOfIntegers.mapAlgEquiv eEL : 𝓞 E →+* 𝓞 EL).comp
        (algebraMap (𝓞 K1) (𝓞 E))
      = (algebraMap (𝓞 K1L) (𝓞 EL)).comp
        (NumberField.RingOfIntegers.mapAlgEquiv eK1 : 𝓞 K1 →+* 𝓞 K1L) := by
    refine RingHom.ext fun a => ?_
    exact mapAlgEquiv_compat eK1 eEL hcompat a
  rw [Ideal.under_def,
    show p'.asIdeal = Ideal.comap (algebraMap (𝓞 K1L) (𝓞 EL)) 𝔮'.asIdeal from h.over,
    Ideal.comap_comap (NumberField.RingOfIntegers.mapAlgEquiv eK1 : 𝓞 K1 →+* 𝓞 K1L)
      (algebraMap (𝓞 K1L) (𝓞 EL)),
    Ideal.comap_comap (algebraMap (𝓞 K1) (𝓞 E))
      (NumberField.RingOfIntegers.mapAlgEquiv eEL : 𝓞 E →+* 𝓞 EL),
    hcomp]

end Helpers

/-- **The split/inert dictionary of the concentrated Grünwald level, transported along an
identification with its image.**

Let `k ⊆ K₁` be a finite Galois extension of number fields, `K₁L ≅ K₁` an isomorphic copy of `K₁`
over `k`, and let `E/K₁` be the concentrated Grünwald extension: a finite Galois extension of
degree `p` which is split completely at every prime of `K₁` over a prime `l` of `k` except the
single prime `u₀`, where it is inert (`e = 1`, `f = p`).  Let `EL` be the image of `E` over `K₁L`,
identified with `E` by a `k`-algebra isomorphism `eEL` compatible with the identification
`eK1 : K₁ ≅ K₁L` (`hcompat`), so that `eK1`, `eEL` identify the pairs `(K₁,u)/(E,𝔮)` with
`(K₁L,p')/(EL,𝔮')`.

Then for every prime `p'` of `𝓞 K₁L` over `l` and every prime `𝔮'` of `𝓞 EL` over `p'`:

* the ramification index of `𝔮'` over `p'` is `1`, and
* its inertia degree over `p'` is `1` if and only if `p'` is not the image `u₀'` of `u₀`.

Route: let `u := Ideal.comap (mapAlgEquiv eK1) p'` and `𝔮 := Ideal.comap (mapAlgEquiv eEL) 𝔮'` be
the transports to `K₁` and `E` (these are primes, `𝔮` lies over `u` by `hcompat`, and `u` lies over
`l` because `p'` does).  The transport lemmas
`Work.SSGRoute.Sha2Lib.ramificationIdx_comap_algEquiv` and
`Work.SSGRoute.Sha2Lib.inertiaDeg_comap_algEquiv` give `e(𝔮'|l) = e(𝔮|l)` and
`f(𝔮'|l) = f(𝔮|l)`, and similarly `e(p'|l) = e(u|l)`, `f(p'|l) = f(u|l)`; tower multiplicativity
(`Ideal.ramificationIdx_tower`, `Ideal.inertiaDeg_tower`) and cancellation of the non-zero
`e(u|l)`, `f(u|l)` give `e(𝔮'|p') = e(𝔮|u)` and `f(𝔮'|p') = f(𝔮|u)`.  Finally `u = u₀` or `u ∈ S`
(by `hSu` and `u` over `l`) and `hsplit`/`hinert` give `e(𝔮|u) = 1` and `f(𝔮|u) = 1 ↔ u ≠ u₀`;
`u = u₀ ↔ p' = u₀'` follows from `hu₀'`, injectivity of `Ideal.map` along the ring equivalence, and
`p ≠ 1` (`Fact p.Prime`). -/
theorem EL_split_inert_dictionary
    {k K1 K1L L E EL : Type} [Field k] [NumberField k] [Field K1] [NumberField K1] [Field K1L]
    [NumberField K1L] [Field L] [NumberField L] [Field E] [NumberField E] [Field EL]
    [NumberField EL]
    [Algebra k K1] [Algebra k K1L] [Algebra k L] [Algebra K1 E] [Algebra K1L EL] [Algebra K1L L]
    [Algebra k E] [Algebra k EL]
    [IsScalarTower k K1 E] [IsScalarTower k K1L EL]
    (p : ℕ) [Fact p.Prime]
    (eK1 : K1 ≃ₐ[k] K1L) (eEL : E ≃ₐ[k] EL)
    (hcompat : ∀ (a : K1) (x : E), eEL (a • x) = eK1 a • eEL x)
    (l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (u₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K1))
    (u₀' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K1L))
    (hu₀' : u₀'.asIdeal = Ideal.map
      ((NumberField.RingOfIntegers.mapAlgEquiv eK1 :
          NumberField.RingOfIntegers K1 ≃ₐ[NumberField.RingOfIntegers k]
            NumberField.RingOfIntegers K1L) : NumberField.RingOfIntegers K1 →+*
          NumberField.RingOfIntegers K1L) u₀.asIdeal)
    (hu₀ : u₀.asIdeal.LiesOver l.asIdeal)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K1)))
    (hSu : ∀ u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K1),
      u.asIdeal.LiesOver l.asIdeal → u ≠ u₀ → u ∈ S)
    (hsplit : ∀ 𝔭 ∈ S, ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E),
      𝔮.asIdeal.LiesOver 𝔭.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K1) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K1) = 1)
    (hinert : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E),
      𝔮.asIdeal.LiesOver u₀.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K1) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K1) = p) :
    ∀ p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K1L),
      p'.asIdeal.LiesOver l.asIdeal →
      ∀ 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers EL),
        𝔮'.asIdeal.LiesOver p'.asIdeal →
          𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K1L) = 1 ∧
          (𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K1L) = 1 ↔ p' ≠ u₀') := by
  intro p' hp'l 𝔮' h𝔮'p'
  -- ## the ring-of-integers transports
  let eK1O : 𝓞 K1 ≃ₐ[𝓞 k] 𝓞 K1L := NumberField.RingOfIntegers.mapAlgEquiv eK1
  let eELO : 𝓞 E ≃ₐ[𝓞 k] 𝓞 EL := NumberField.RingOfIntegers.mapAlgEquiv eEL
  have hu₀'' : u₀'.asIdeal = Ideal.map (eK1O : 𝓞 K1 →+* 𝓞 K1L) u₀.asIdeal := hu₀'
  -- ## the transported primes
  let u : IsDedekindDomain.HeightOneSpectrum (𝓞 K1) :=
    IsDedekindDomain.HeightOneSpectrum.comap (eK1O : 𝓞 K1 →+* 𝓞 K1L) eK1O.surjective p'
  let q : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
    IsDedekindDomain.HeightOneSpectrum.comap (eELO : 𝓞 E →+* 𝓞 EL) eELO.surjective 𝔮'
  have hu_ideal : u.asIdeal = Ideal.comap (eK1O : 𝓞 K1 →+* 𝓞 K1L) p'.asIdeal := rfl
  have hq_ideal : q.asIdeal = Ideal.comap (eELO : 𝓞 E →+* 𝓞 EL) 𝔮'.asIdeal := rfl
  -- ## `q` lies over `u`
  have hq_over_u : q.asIdeal.LiesOver u.asIdeal :=
    liesOver_comap_transport eK1 eEL hcompat p' 𝔮' h𝔮'p'
  -- ## instances for downstream use
  haveI hp'lI : p'.asIdeal.LiesOver l.asIdeal := hp'l
  haveI h𝔮'p'I : 𝔮'.asIdeal.LiesOver p'.asIdeal := h𝔮'p'
  haveI hq_uI : q.asIdeal.LiesOver u.asIdeal := hq_over_u
  haveI h𝔮'lI : 𝔮'.asIdeal.LiesOver l.asIdeal :=
    Ideal.LiesOver.trans 𝔮'.asIdeal p'.asIdeal l.asIdeal
  -- ## `u` lies over `l`
  have hu_over_l : u.asIdeal.LiesOver l.asIdeal := by
    refine ⟨?_⟩
    have hcomp : (eK1O : 𝓞 K1 →+* 𝓞 K1L).comp (algebraMap (𝓞 k) (𝓞 K1))
        = algebraMap (𝓞 k) (𝓞 K1L) := by
      refine RingHom.ext fun c => ?_
      exact eK1O.commutes c
    rw [hu_ideal, Ideal.under_def, Ideal.comap_comap, hcomp]
    exact hp'l.over
  -- ## transport of the ramification indices and inertia degrees
  have hram_E : q.asIdeal.ramificationIdx (𝓞 k) = 𝔮'.asIdeal.ramificationIdx (𝓞 k) :=
    Work.SSGRoute.Sha2Lib.ramificationIdx_comap_algEquiv E EL eELO l 𝔮'.asIdeal
  have hram_K1 : u.asIdeal.ramificationIdx (𝓞 k) = p'.asIdeal.ramificationIdx (𝓞 k) :=
    Work.SSGRoute.Sha2Lib.ramificationIdx_comap_algEquiv K1 K1L eK1O l p'.asIdeal
  have hf_E : q.asIdeal.inertiaDeg (𝓞 k) = 𝔮'.asIdeal.inertiaDeg (𝓞 k) :=
    Work.SSGRoute.Sha2Lib.inertiaDeg_comap_algEquiv E EL eELO l 𝔮'.asIdeal
  have hf_K1 : u.asIdeal.inertiaDeg (𝓞 k) = p'.asIdeal.inertiaDeg (𝓞 k) :=
    Work.SSGRoute.Sha2Lib.inertiaDeg_comap_algEquiv K1 K1L eK1O l p'.asIdeal
  -- ## tower multiplicativity
  have hram_A : q.asIdeal.ramificationIdx (𝓞 k)
      = u.asIdeal.ramificationIdx (𝓞 k) * q.asIdeal.ramificationIdx (𝓞 K1) :=
    Ideal.ramificationIdx_tower u.asIdeal q.asIdeal
  have hram_B : 𝔮'.asIdeal.ramificationIdx (𝓞 k)
      = p'.asIdeal.ramificationIdx (𝓞 k) * 𝔮'.asIdeal.ramificationIdx (𝓞 K1L) :=
    Ideal.ramificationIdx_tower p'.asIdeal 𝔮'.asIdeal
  have hf_A : q.asIdeal.inertiaDeg (𝓞 k)
      = u.asIdeal.inertiaDeg (𝓞 k) * q.asIdeal.inertiaDeg (𝓞 K1) :=
    Ideal.inertiaDeg_tower u.asIdeal q.asIdeal
  have hf_B : 𝔮'.asIdeal.inertiaDeg (𝓞 k)
      = p'.asIdeal.inertiaDeg (𝓞 k) * 𝔮'.asIdeal.inertiaDeg (𝓞 K1L) :=
    Ideal.inertiaDeg_tower p'.asIdeal 𝔮'.asIdeal
  -- ## cancellation of the non-zero global invariants of `u`
  have hram_pos : 0 < u.asIdeal.ramificationIdx (𝓞 k) :=
    Ideal.ramificationIdx_pos (𝓞 k) u.asIdeal
  have hf_pos : 0 < u.asIdeal.inertiaDeg (𝓞 k) :=
    Ideal.inertiaDeg_pos u.asIdeal (𝓞 k)
  have hram_local : q.asIdeal.ramificationIdx (𝓞 K1) = 𝔮'.asIdeal.ramificationIdx (𝓞 K1L) := by
    refine Nat.mul_left_cancel hram_pos ?_
    calc u.asIdeal.ramificationIdx (𝓞 k) * q.asIdeal.ramificationIdx (𝓞 K1)
        = q.asIdeal.ramificationIdx (𝓞 k) := hram_A.symm
      _ = 𝔮'.asIdeal.ramificationIdx (𝓞 k) := hram_E
      _ = p'.asIdeal.ramificationIdx (𝓞 k) * 𝔮'.asIdeal.ramificationIdx (𝓞 K1L) := hram_B
      _ = u.asIdeal.ramificationIdx (𝓞 k) * 𝔮'.asIdeal.ramificationIdx (𝓞 K1L) := by
            rw [hram_K1]
  have hf_local : q.asIdeal.inertiaDeg (𝓞 K1) = 𝔮'.asIdeal.inertiaDeg (𝓞 K1L) := by
    refine Nat.mul_left_cancel hf_pos ?_
    calc u.asIdeal.inertiaDeg (𝓞 k) * q.asIdeal.inertiaDeg (𝓞 K1)
        = q.asIdeal.inertiaDeg (𝓞 k) := hf_A.symm
      _ = 𝔮'.asIdeal.inertiaDeg (𝓞 k) := hf_E
      _ = p'.asIdeal.inertiaDeg (𝓞 k) * 𝔮'.asIdeal.inertiaDeg (𝓞 K1L) := hf_B
      _ = u.asIdeal.inertiaDeg (𝓞 k) * 𝔮'.asIdeal.inertiaDeg (𝓞 K1L) := by
            rw [hf_K1]
  -- ## the split/inert hypotheses at `u`
  have hq_local_ram : q.asIdeal.ramificationIdx (𝓞 K1) = 1 := by
    by_cases hu : u = u₀
    · have h : q.asIdeal.LiesOver u₀.asIdeal := by rw [← hu]; exact hq_over_u
      exact (hinert q h).1
    · exact (hsplit u (hSu u hu_over_l hu) q hq_over_u).1
  have hq_local_inert : q.asIdeal.inertiaDeg (𝓞 K1) = 1 ↔ u ≠ u₀ := by
    constructor
    · intro h1 hu_eq
      have h : q.asIdeal.LiesOver u₀.asIdeal := by rw [← hu_eq]; exact hq_over_u
      have hp : q.asIdeal.inertiaDeg (𝓞 K1) = p := (hinert q h).2
      exact (Fact.out : p.Prime).ne_one (hp ▸ h1)
    · intro hne
      exact (hsplit u (hSu u hu_over_l hne) q hq_over_u).2
  -- ## `u = u₀` iff `p' = u₀'`
  have huu₀_iff : u = u₀ ↔ p' = u₀' := by
    constructor
    · intro hu
      have h1 : u₀.asIdeal = Ideal.comap (eK1O : 𝓞 K1 →+* 𝓞 K1L) p'.asIdeal := by
        rw [← hu, hu_ideal]
      have key : u₀'.asIdeal = p'.asIdeal := by
        rw [hu₀'', h1,
          Ideal.map_comap_of_surjective (eK1O : 𝓞 K1 →+* 𝓞 K1L) eK1O.surjective p'.asIdeal]
      exact IsDedekindDomain.HeightOneSpectrum.ext key.symm
    · intro hp
      have key : u.asIdeal = u₀.asIdeal := by
        rw [hu_ideal, hp, hu₀'']
        have hne : Ideal.map (eK1O : 𝓞 K1 →+* 𝓞 K1L) u₀.asIdeal ≠ ⊤ := by
          rw [← hu₀'']; exact u₀'.isPrime.ne_top
        rw [Ideal.comap_map_eq_self_of_isMaximal (eK1O : 𝓞 K1 →+* 𝓞 K1L) hne]
      exact IsDedekindDomain.HeightOneSpectrum.ext key
  refine ⟨?_, ?_⟩
  · rw [← hram_local, hq_local_ram]
  · exact Iff.trans (by rw [hf_local]) (hq_local_inert.trans huu₀_iff.not)

end Work.SSGRoute.TPatom
