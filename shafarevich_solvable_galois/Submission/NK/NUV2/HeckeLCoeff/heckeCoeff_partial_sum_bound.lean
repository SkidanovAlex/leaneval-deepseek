import Mathlib
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.HeckeLCoeff

open Filter Finset
open scoped Topology BigOperators Classical
open NumberField

set_option linter.dupNamespace false
set_option linter.style.haveILetI false

/-!
## The partial sums of the Hecke coefficients

`heckeCoeff K U S χ n` is the sum of `χ(𝔞)` over the ideals `𝔞` of `𝓞 K` which are nonzero,
coprime to `S`, and of absolute norm `n`.  Its partial sums `∑_{n ≤ N} heckeCoeff n` are therefore
`∑_{N𝔞 ≤ N} χ(class 𝔞)`, and grouping the ideals by their class `c` in the (finite) ray class group
gives `∑_c χ(c) · A_c(N)` with `A_c(N) = #{𝔞 : class 𝔞 = c, N𝔞 ≤ N}`.  Since `χ ≠ 1`, the sum of
`χ` over the group vanishes, so we may replace `A_c(N)` by `A_c(N) - A_1(N)` for a fixed class, and
the hypothesis `hC` bounds each of those differences by `C · N^{1-1/[K:ℚ]}`.

This file proves the required `NK.NUV2.HeckeLCoeff.heckeCoeff_partial_sum_bound` by carrying out
that grouping.
-/

/-- The nonzero ideals of `𝓞 K` which are coprime to every prime in `S` and of absolute norm
`≤ N`. -/
noncomputable def idealFinset (K : Type) [Field K] [NumberField K]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (N : ℕ) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset).filter
    (fun I => I ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I)

/-- The nonzero ideals of `𝓞 K` which are coprime to every prime in `S` and of absolute norm
exactly `k`. -/
noncomputable def normFibre (K : Type) [Field K] [NumberField K]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (k : ℕ) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k).toFinset).filter
    (fun I => I ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I)

/-- The ideals counted by `idealFinset K S N` whose class in the ray class group is `c`. -/
noncomputable def classCount (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (S : Finset (NK.HeckeL.PrimeIdeal K)) (N : ℕ)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℕ :=
  ((idealFinset K S N).filter (fun I => NK.HeckeL.classOfIdeal K U I = c)).card

/-- The ideals of absolute norm exactly `k` counted by `normFibre K S k` whose class is `c`. -/
noncomputable def fibreClassCount (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (S : Finset (NK.HeckeL.PrimeIdeal K)) (k : ℕ)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℕ :=
  ((normFibre K S k).filter (fun I => NK.HeckeL.classOfIdeal K U I = c)).card

/-! ### The sum of a non-trivial complex character over a finite group vanishes -/

/-- The sum of the values of a non-trivial homomorphism from a finite group to `ℂ` vanishes. -/
theorem sum_monoidHom_complex_eq_zero {G : Type*} [CommGroup G] [Fintype G]
    {f : G →* ℂ} (hf : f ≠ 1) : ∑ g : G, f g = 0 := by
  obtain ⟨b, hb⟩ : ∃ b : G, f b ≠ 1 := by
    by_contra h
    push Not at h
    exact hf (MonoidHom.ext h)
  have h1 : ∑ g : G, f g = f b * ∑ g : G, f g := by
    have hA : f b * ∑ g : G, f g = ∑ g : G, f (b * g) := by
      rw [Finset.mul_sum]
      exact (Finset.sum_congr rfl (fun g _ => map_mul f b g)).symm
    rw [hA]
    exact (Equiv.sum_comp (Equiv.mulLeft b) f).symm
  have h2 : (f b - 1) * (∑ g : G, f g) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hb)

/-- The sum of the values of a non-trivial ray class character over the (finite) ray class group
vanishes. -/
theorem sum_toComplex_eq_zero (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K))
    [Fintype (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (χ : NK.HeckeL.RayChar K U) (hχ : χ ≠ 1) :
    ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U, χ.toComplex c = 0 := by
  refine sum_monoidHom_complex_eq_zero (f := χ.toComplex) ?_
  intro h
  apply hχ
  apply MonoidHom.ext
  intro c
  apply Units.ext
  have := congrArg (fun g : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U →* ℂ => g c) h
  simpa [NK.HeckeL.RayChar.toComplex] using this

/-! ### Grouping the coefficients by the norm and then by the ray class -/

/-- The coefficient `heckeCoeff K U S χ k` is the finite sum of `χ(𝔞)` over the ideals of norm
exactly `k`. -/
theorem heckeCoeff_eq_sum_normFibre (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (S : Finset (NK.HeckeL.PrimeIdeal K))
    (χ : NK.HeckeL.RayChar K U) (k : ℕ) :
    NK.HeckeL.heckeCoeff K U S χ k = ∑ I ∈ normFibre K S k, χ.atIdeal I := by
  classical
  haveI hfin : Finite {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ Ideal.absNorm 𝔞 = k} :=
    Set.Finite.to_subtype (Set.Finite.subset (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k)
      (fun I hI => hI.2.2))
  letI : Fintype {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ Ideal.absNorm 𝔞 = k} := Fintype.ofFinite _
  rw [NK.HeckeL.heckeCoeff, tsum_fintype]
  refine (Finset.sum_subtype (normFibre K S k) ?_ (fun I => χ.atIdeal I)).symm
  intro I
  simp only [normFibre, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

/-- Splitting the sum over the ideals of norm `k` according to their class in the ray class group
turns it into `∑_c χ(c) · #{𝔞 of norm k in class c}`. -/
theorem sum_normFibre_eq (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K))
    [Fintype (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) (k : ℕ) :
    ∑ I ∈ normFibre K S k, χ.atIdeal I =
      ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        (fibreClassCount K U S k c : ℂ) * χ.toComplex c := by
  classical
  rw [← Finset.sum_fiberwise (normFibre K S k) (fun I => NK.HeckeL.classOfIdeal K U I)
    (fun I => χ.atIdeal I)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have key : ∀ I ∈ (normFibre K S k).filter (fun I => NK.HeckeL.classOfIdeal K U I = c),
      χ.atIdeal I = χ.toComplex c := by
    intro I hI
    simp only [Finset.mem_filter] at hI
    rw [NK.HeckeL.RayChar.atIdeal_apply, hI.2]
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The nonzero, coprime ideals of norm `≤ N` are the disjoint union, over `1 ≤ k ≤ N`, of those
of norm exactly `k`. -/
theorem idealFinset_eq_biUnion (K : Type) [Field K] [NumberField K]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (N : ℕ) :
    idealFinset K S N = (Finset.Icc 1 N).biUnion (fun k => normFibre K S k) := by
  classical
  ext I
  simp only [idealFinset, normFibre, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨hN, h1, h2⟩
    exact ⟨Ideal.absNorm I,
      ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => h1 (Ideal.absNorm_eq_zero_iff.mp h)), hN⟩,
        rfl, h1, h2⟩⟩
  · rintro ⟨k, ⟨hk1, hk2⟩, h1, h2, hk⟩
    exact ⟨h1 ▸ hk2, h2, hk⟩

/-- The count of ideals of norm `≤ N` in a fixed ray class is the sum, over `k ≤ N`, of the counts
of ideals of norm exactly `k` in that class. -/
theorem classCount_eq_sum (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (S : Finset (NK.HeckeL.PrimeIdeal K)) (N : ℕ)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) :
    classCount K U S N c = ∑ k ∈ Finset.Icc 1 N, fibreClassCount K U S k c := by
  classical
  unfold classCount
  rw [idealFinset_eq_biUnion K S N, Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · rfl
  · intro k hk l hl hkl
    change Disjoint ((normFibre K S k).filter (fun I => NK.HeckeL.classOfIdeal K U I = c))
      ((normFibre K S l).filter (fun I => NK.HeckeL.classOfIdeal K U I = c))
    rw [Finset.disjoint_left]
    intro I hIk hIl
    simp only [normFibre, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hIk hIl
    exact hkl (by rw [← hIk.1.1, hIl.1.1])

/-- The finset count `classCount K U S N c` computes the `Nat.card` of the corresponding subtype,
which is the counting function appearing in the equidistribution hypothesis. -/
theorem classCount_eq_natCard (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (S : Finset (NK.HeckeL.PrimeIdeal K)) (N : ℕ)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) :
    (classCount K U S N c : ℝ) =
      (Nat.card {I : Ideal (𝓞 K) //
        I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
          NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ (N : ℝ)} : ℝ) := by
  classical
  have h1 : Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
        NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ (N : ℝ)}
      = Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
        NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ N} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun I => by
      exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, Nat.cast_le.mp h.2.2.2⟩,
             fun h => ⟨h.1, h.2.1, h.2.2.1, Nat.cast_le.mpr h.2.2.2⟩⟩))
  haveI hfin : Finite {I : Ideal (𝓞 K) // I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
      NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ N} :=
    Set.Finite.to_subtype (Set.Finite.subset (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N)
      (fun I hI => hI.2.2.2))
  letI : Fintype {I : Ideal (𝓞 K) // I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
      NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ N} := Fintype.ofFinite _
  have hF : ∀ I, I ∈ (idealFinset K S N).filter (fun I => NK.HeckeL.classOfIdeal K U I = c) ↔
      (I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
        NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ N) := by
    intro I
    simp only [idealFinset, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto
  have hcard : ((idealFinset K S N).filter
        (fun I => NK.HeckeL.classOfIdeal K U I = c)).card
      = Fintype.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
        NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ N} := by
    rw [Fintype.card_eq_sum_ones, ← Finset.sum_subtype _ hF (fun _ => (1 : ℕ)),
      Finset.card_eq_sum_ones]
  have key : Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧
      NK.HeckeL.classOfIdeal K U I = c ∧ Ideal.absNorm I ≤ N} = classCount K U S N c := by
    rw [Nat.card_eq_fintype_card, ← hcard]
    rfl
  rw [h1, key]

/-- **The partial sums of the Hecke `L`-series coefficients `heckeCoeff K U S χ` are `O(N^θ)` with
`θ = 1 - 1/[K:ℚ]`, assuming the equidistribution hypothesis `hC` that any two ray classes have
their ideal-counting functions agreeing up to `O(X^θ)`.  The proof groups the ideals of norm `≤ N`
by their class in the ray class group: the character values `χ(c)` multiply the counts, and since
`χ ≠ 1` the sum `∑_c χ(c)` vanishes, so only the differences of the counts survive, and those are
bounded by `hC`. -/
theorem heckeCoeff_partial_sum_bound (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K))
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) (hχ : χ ≠ 1)
    (hC : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        |((Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ)
        - (Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ))|
      ≤ C * X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ N : ℕ, 1 ≤ N →
      ‖∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k‖
        ≤ C' * (N : ℝ) ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  classical
  letI : Fintype (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) := Fintype.ofFinite _
  obtain ⟨C, hCpos, hCbd⟩ := hC
  have hθnn : 0 ≤ (1 : ℝ) - 1 / (Module.finrank ℚ K : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      have := Module.finrank_pos (R := ℚ) (M := K)
      exact_mod_cast this
    have hpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by linarith
    rw [sub_nonneg, div_le_one hpos]
    exact h1
  refine ⟨max 1 ((Nat.card (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℝ) * C),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun N hN => ?_⟩
  have hsum : ∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k
      = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          (classCount K U S N c : ℂ) * χ.toComplex c := by
    calc ∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k
        = ∑ k ∈ Finset.Icc 1 N, ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (fibreClassCount K U S k c : ℂ) * χ.toComplex c := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [heckeCoeff_eq_sum_normFibre K U S χ k, sum_normFibre_eq K U S χ k]
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            ∑ k ∈ Finset.Icc 1 N, (fibreClassCount K U S k c : ℂ) * χ.toComplex c :=
          Finset.sum_comm
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (∑ k ∈ Finset.Icc 1 N, (fibreClassCount K U S k c : ℂ)) * χ.toComplex c := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [← Finset.sum_mul]
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (classCount K U S N c : ℂ) * χ.toComplex c := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          refine congrArg (fun x : ℂ => x * χ.toComplex c) ?_
          rw [classCount_eq_sum K U S N c, Nat.cast_sum]
  have hzero : ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
      (classCount K U S N 1 : ℂ) * χ.toComplex c = 0 := by
    rw [← Finset.mul_sum, sum_toComplex_eq_zero K U χ hχ, mul_zero]
  have hdiff : ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        (classCount K U S N c : ℂ) * χ.toComplex c
      = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        ((classCount K U S N c : ℂ) - (classCount K U S N 1 : ℂ)) * χ.toComplex c := by
    rw [← sub_eq_zero]
    calc (∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (classCount K U S N c : ℂ) * χ.toComplex c)
          - ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            ((classCount K U S N c : ℂ) - (classCount K U S N 1 : ℂ)) * χ.toComplex c
        = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            ((classCount K U S N c : ℂ) * χ.toComplex c
              - ((classCount K U S N c : ℂ) - (classCount K U S N 1 : ℂ)) * χ.toComplex c) :=
          (Finset.sum_sub_distrib _ _).symm
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (classCount K U S N 1 : ℂ) * χ.toComplex c :=
          Finset.sum_congr rfl (fun c _ => by ring)
      _ = 0 := hzero
  have hbd : ∀ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
      ‖((classCount K U S N c : ℂ) - (classCount K U S N 1 : ℂ)) * χ.toComplex c‖
        ≤ C * (N : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
    intro c
    have hnorm : ‖((classCount K U S N c : ℂ) - (classCount K U S N 1 : ℂ))‖
        = |(classCount K U S N c : ℝ) - (classCount K U S N 1 : ℝ)| := by
      have hcast : ((classCount K U S N c : ℂ) - (classCount K U S N 1 : ℂ))
          = ((((classCount K U S N c : ℝ) - (classCount K U S N 1 : ℝ)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast]
      exact RCLike.norm_ofReal _
    rw [norm_mul, NK.HeckeL.RayChar.norm_toComplex_apply_eq_one, mul_one, hnorm]
    have h := hCbd (N : ℝ) (by exact_mod_cast hN) c 1
    rw [← classCount_eq_natCard K U S N c, ← classCount_eq_natCard K U S N 1] at h
    exact h
  calc ‖∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k‖
      = ‖∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          (classCount K U S N c : ℂ) * χ.toComplex c‖ := by rw [hsum]
    _ = ‖∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          ((classCount K U S N c : ℂ) - (classCount K U S N 1 : ℂ)) * χ.toComplex c‖ := by
        rw [hdiff]
    _ ≤ ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          C * (N : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => hbd c))
    _ = ((Nat.card (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℝ) * C)
          * (N : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        ring
    _ ≤ max 1 ((Nat.card (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℝ) * C)
          * (N : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end NK.NUV2.HeckeLCoeff
