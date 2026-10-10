import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Work.LocalFields.Residue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero Topology

/-- The canonical reduction map `𝓞 K →+* κ_v` of a number field at a finite prime `v` is
surjective: the residue field of the `v`-adic completion agrees with the residue field
`𝓞 K ⧸ v` of `𝓞 K` at `v`.

The proof approximates an element `a` of the ring of integers `𝒪_v` of the completion by an
element `k` of `K` (using that `K` is dense in its completion), then approximates `k` by an
element `s` of `𝓞 K` (using `exists_valuation_sub_lt_of_integer`), the approximation being fine
enough that `s ≡ a (mod 𝔪_v)`. -/
theorem residueMap_surjective {K : Type*} [Field K] [NumberField K]
    (v : Work.LocalFields.FinitePrime K) :
    Function.Surjective (Work.LocalFields.residueMap v) := by
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  have key : ∃ x : 𝓞 K, IsLocalRing.residue (Work.LocalFields.intRing K v)
      (algebraMap (𝓞 K) (Work.LocalFields.intRing K v) x) =
      IsLocalRing.residue (Work.LocalFields.intRing K v) a := by
    -- `K` is dense in its `v`-adic completion.
    have hd : DenseRange (fun x : K => (x : Work.LocalFields.Completion K v)) :=
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v
    -- The basic open neighbourhood `a + 𝔪_v` of `a`.
    have hnb : ({z : Work.LocalFields.Completion K v | Valued.v (z - ↑a) < 1} : Set _) ∈
        𝓝 (↑a : Work.LocalFields.Completion K v) := by
      rw [Valued.mem_nhds]
      refine ⟨1, ?_⟩
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding] at hz
      simpa using hz
    -- An element `k` of `K` congruent to `a` modulo `𝔪_v`.
    obtain ⟨k, hk⟩ := hd.mem_nhds hnb
    have hk' : Valued.v ((k : Work.LocalFields.Completion K v) - ↑a) < 1 := hk
    have hka : Valued.v (↑a : Work.LocalFields.Completion K v) ≤ 1 :=
      (Valuation.mem_integer_iff _ _).mp a.2
    -- `k` is `v`-adically integral.
    have hkval : v.valuation K k ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k]
      calc Valued.v (k : Work.LocalFields.Completion K v)
          = Valued.v (((k : Work.LocalFields.Completion K v) - ↑a) + ↑a) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v ((k : Work.LocalFields.Completion K v) - ↑a))
              (Valued.v (↑a : Work.LocalFields.Completion K v)) := Valuation.map_add ..
        _ ≤ 1 := max_le hk'.le hka
    -- An algebraic integer `s` congruent to `k` modulo `𝔪_v`.
    obtain ⟨s, hs⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
      v hkval (1 : (ℤᵐ⁰)ˣ)
    refine ⟨s, ?_⟩
    -- It suffices that `s - a ∈ 𝔪_v`, i.e. `v(s - a) < 1`.
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    refine (Valuation.mem_maximalIdeal_iff _ _).mpr ?_
    have hcoe : (↑(algebraMap (𝓞 K) (Work.LocalFields.intRing K v) s - a) :
        Work.LocalFields.Completion K v) =
        (s : Work.LocalFields.Completion K v) - (↑a : Work.LocalFields.Completion K v) := by
      change (Work.LocalFields.intRing K v).subtype
        (algebraMap (𝓞 K) (Work.LocalFields.intRing K v) s - a) = _
      rw [map_sub]
      rfl
    rw [hcoe]
    have h1 : Valued.v ((s : Work.LocalFields.Completion K v) -
        (k : Work.LocalFields.Completion K v)) < 1 := by
      rw [show ((s : Work.LocalFields.Completion K v) - (k : Work.LocalFields.Completion K v)) =
          (((s : K) - k : K) : Work.LocalFields.Completion K v) from by
        rw [← NumberField.FinitePlace.embedding_apply (v := v) (s : K),
            ← NumberField.FinitePlace.embedding_apply (v := v) k,
            ← NumberField.FinitePlace.embedding_apply (v := v) ((s : K) - k),
            ← map_sub]]
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using hs
    have h2 : Valued.v ((k : Work.LocalFields.Completion K v) - ↑a) < 1 := hk'
    rw [show (s : Work.LocalFields.Completion K v) - ↑a =
        ((s : Work.LocalFields.Completion K v) - (k : Work.LocalFields.Completion K v)) +
        ((k : Work.LocalFields.Completion K v) - ↑a) from by ring]
    exact lt_of_le_of_lt (Valuation.map_add ..) (max_lt h1 h2)
  obtain ⟨x, hx⟩ := key
  exact ⟨x, hx⟩

end Work.LocalFields
