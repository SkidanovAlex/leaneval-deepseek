import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.Hcond_joinPart
import Submission.Work.EKLComp.hPart_exists_refining
import Submission.Work.EKLComp.Hpart.tendsto_Hcond_iSup
import Submission.Work.EKLComp.hPart_Hcond

/-!
# Definitions and basic σ-algebra API for EKL Prop 9.2 (`prop92`)
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

noncomputable section
namespace Work.EKLComp
open Work.EKLContract

set_option maxHeartbeats 1000000

/-! ## The shift maps `x ↦ aZ t k • x` -/

/-- The map `x ↦ aZ t k • x`. -/
def shiftZ (t : Fin 3 → ℝ) (k : ℤ) : X3 → X3 := fun x => aZ t k • x

theorem measurable_shiftZ (t : Fin 3 → ℝ) (k : ℤ) : Measurable (shiftZ t k) := by
  unfold shiftZ; fun_prop

theorem shiftZ_zero (t : Fin 3 → ℝ) : shiftZ t 0 = id := by
  funext x; simp [shiftZ, aZ_zero]

theorem shiftZ_add (t : Fin 3 → ℝ) (k l : ℤ) : shiftZ t (k + l) = shiftZ t k ∘ shiftZ t l := by
  funext x
  simp only [Function.comp_apply, shiftZ, ← mul_smul, aZ_add]

/-- `shiftZ t k` is a bijection. -/
theorem bijective_shiftZ (t : Fin 3 → ℝ) (k : ℤ) : Function.Bijective (shiftZ t k) := by
  refine ⟨fun x y h => ?_, fun y => ⟨aZ t (-k) • y, ?_⟩⟩
  · have h2 : aZ t (-k) • (aZ t k • x) = aZ t (-k) • (aZ t k • y) := by
      have h' : shiftZ t k x = shiftZ t k y := h
      exact congrArg (fun z => aZ t (-k) • z) h'
    rw [← mul_smul, ← mul_smul] at h2
    have h1 : aZ t (-k) * aZ t k = 1 := by simpa using aZ_mul_neg t (-k)
    rw [h1, one_smul, one_smul] at h2
    exact h2
  · show aZ t k • (aZ t (-k) • y) = y
    rw [← mul_smul, aZ_mul_neg, one_smul]

/-- `Bsig t P k`, the pullback of `partSigma P` along `x ↦ aZ t k • x`. -/
def Bsig (t : Fin 3 → ℝ) (P : FinPart X3) (k : ℤ) : MeasurableSpace X3 :=
  MeasurableSpace.comap (shiftZ t k) (partSigma P)

theorem comap_shiftZ_Bsig (t : Fin 3 → ℝ) (P : FinPart X3) (k l : ℤ) :
    MeasurableSpace.comap (shiftZ t k) (Bsig t P l) = Bsig t P (k + l) := by
  unfold Bsig
  rw [MeasurableSpace.comap_comp, ← shiftZ_add, add_comm]

/-! ## Pullback partitions -/

/-- The pullback of `P` along `x ↦ aZ t k • x`. -/
def vpartZ (t : Fin 3 → ℝ) (k : ℤ) (P : FinPart X3) : FinPart X3 where
  n := P.n
  parts i := (shiftZ t k) ⁻¹' P.parts i
  measurable i := (P.measurable i).preimage (measurable_shiftZ t k)
  disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    exact Set.disjoint_left.mp (P.disjoint hij) hx hy
  cover := by
    rw [← Set.preimage_iUnion, P.cover, Set.preimage_univ]

@[simp] theorem vpartZ_parts (t : Fin 3 → ℝ) (k : ℤ) (P : FinPart X3) (i : Fin P.n) :
    (vpartZ t k P).parts i = (shiftZ t k) ⁻¹' P.parts i := rfl

theorem partSigma_eq_generateFrom (P : FinPart X3) :
    partSigma P = MeasurableSpace.generateFrom (Set.range P.parts) := rfl

theorem partSigma_vpartZ (t : Fin 3 → ℝ) (k : ℤ) (P : FinPart X3) :
    partSigma (vpartZ t k P) = Bsig t P k := by
  rw [partSigma_eq_generateFrom, Bsig, partSigma_eq_generateFrom,
    MeasurableSpace.comap_generateFrom]
  congr 1
  rw [← Set.range_comp]
  rfl

/-! ## The two-sided window partition -/

theorem winPart_measurable (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ)
    (i : Fin (P.n ^ (2 * m + 1))) :
    MeasurableSet (⋂ j : Fin (2 * m + 1),
      (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
        ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j)) :=
  MeasurableSet.iInter fun j => (P.measurable _).preimage (measurable_shiftZ t _)

theorem winPart_disjoint (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    Pairwise (fun i i' : Fin (P.n ^ (2 * m + 1)) =>
      Disjoint (⋂ j : Fin (2 * m + 1),
          (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
            ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j))
        (⋂ j : Fin (2 * m + 1),
          (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
            ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i' j))) := by
  intro i i' hii'
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [Set.mem_iInter, Set.mem_preimage] at hx hx'
  have hne : (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i ≠
      (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i' := by
    intro h
    exact hii' ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm.injective h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  exact Set.disjoint_left.mp (P.disjoint hj) (hx j) (hx' j)

theorem winPart_cover (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    (⋃ i : Fin (P.n ^ (2 * m + 1)), ⋂ j : Fin (2 * m + 1),
      (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
        ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  have hchoice : ∀ j : Fin (2 * m + 1), ∃ c : Fin P.n,
      shiftZ t ((j : ℤ) - (m : ℤ)) x ∈ P.parts c := by
    intro j
    have h : shiftZ t ((j : ℤ) - (m : ℤ)) x ∈ ⋃ c, P.parts c := by rw [P.cover]; trivial
    simpa using h
  choose c hc using hchoice
  refine Set.mem_iUnion.mpr ⟨(finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)) c, ?_⟩
  simp only [Set.mem_iInter, Set.mem_preimage]
  intro j
  rw [Equiv.symm_apply_apply]
  exact hc j

/-- The two-sided window partition `⋁_{|k| ≤ m} (aZ t k)⁻¹ P`. -/
def winPart (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) : FinPart X3 where
  n := P.n ^ (2 * m + 1)
  parts := fun i => ⋂ j : Fin (2 * m + 1),
    (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
      ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j)
  measurable := winPart_measurable t P m
  disjoint := winPart_disjoint t P m
  cover := winPart_cover t P m

@[simp] theorem winPart_parts (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ)
    (i : Fin (P.n ^ (2 * m + 1))) :
    (winPart t P m).parts i = ⋂ j : Fin (2 * m + 1),
      (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
        ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j) := rfl


/-! ## The σ-algebra of the window -/

/-- `winIdx P m i j` is the `j`-th coordinate of the atom with index `i`. -/
def winIdx (P : FinPart X3) (m : ℕ) : Fin (P.n ^ (2 * m + 1)) → Fin (2 * m + 1) → Fin P.n :=
  fun i => (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i

theorem winPart_parts' (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ)
    (i : Fin (P.n ^ (2 * m + 1))) :
    (winPart t P m).parts i = ⋂ j : Fin (2 * m + 1),
      (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts (winIdx P m i j) := rfl

/-- The generator `(shiftZ t k)⁻¹ P.parts c` belongs to `Bsig t P k`. -/
theorem Bsig_generator_mem (t : Fin 3 → ℝ) (P : FinPart X3) (k : ℤ) (c : Fin P.n) :
    (Bsig t P k).MeasurableSet' ((shiftZ t k) ⁻¹' P.parts c) := by
  rw [Bsig, partSigma_eq_generateFrom]
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨P.parts c, MeasurableSpace.measurableSet_generateFrom ⟨c, rfl⟩, rfl⟩

/-- Each generator of `⨆_j Bsig t P (j - m)` is a union of window atoms. -/
theorem generator_mem_partSigma_winPart (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ)
    (j₀ : Fin (2 * m + 1)) (c : Fin P.n) :
    (partSigma (winPart t P m)).MeasurableSet' ((shiftZ t ((j₀ : ℤ) - (m : ℤ))) ⁻¹' P.parts c) := by
  have hset : (shiftZ t ((j₀ : ℤ) - (m : ℤ))) ⁻¹' P.parts c =
      ⋃ i : Fin (P.n ^ (2 * m + 1)),
        (if (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j₀ = c
          then (winPart t P m).parts i else ∅) := by
    ext x
    constructor
    · intro hx
      have hchoice : ∀ j : Fin (2 * m + 1), ∃ cc : Fin P.n,
          shiftZ t ((j : ℤ) - (m : ℤ)) x ∈ P.parts cc := by
        intro j
        have h : shiftZ t ((j : ℤ) - (m : ℤ)) x ∈ ⋃ cc, P.parts cc := by rw [P.cover]; trivial
        simpa using h
      choose d hd using hchoice
      have hdj : d j₀ = c := by
        by_contra hne
        exact Set.disjoint_left.mp (P.disjoint hne) (hd j₀) hx
      rw [Set.mem_iUnion]
      refine ⟨(finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)) d, ?_⟩
      have hcond : (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm
          ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)) d) j₀ = c := by
        rw [Equiv.symm_apply_apply]; exact hdj
      rw [if_pos hcond]
      rw [winPart_parts]
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro j
      rw [Equiv.symm_apply_apply]
      exact hd j
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      by_cases hc : (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j₀ = c
      · rw [if_pos hc] at hi
        rw [winPart_parts] at hi
        simp only [Set.mem_iInter, Set.mem_preimage] at hi
        have h := hi j₀
        rw [hc] at h
        exact h
      · rw [if_neg hc] at hi
        exact absurd hi (by simp)
  rw [hset]
  exact @MeasurableSet.iUnion X3 (Fin (P.n ^ (2 * m + 1))) (partSigma (winPart t P m)) _
    (fun i => (if (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j₀ = c
      then (winPart t P m).parts i else ∅)) (fun i => by
    by_cases hc : (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j₀ = c
    · rw [if_pos hc]
      exact MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩
    · rw [if_neg hc]; exact @MeasurableSet.empty X3 (partSigma (winPart t P m)))

theorem partSigma_winPart_le (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    partSigma (winPart t P m) ≤ ⨆ j : Fin (2 * m + 1), Bsig t P ((j : ℤ) - (m : ℤ)) := by
  rw [partSigma_eq_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, rfl⟩
  have hf : ∀ j : Fin (2 * m + 1),
      ((⨆ j : Fin (2 * m + 1), Bsig t P ((j : ℤ) - (m : ℤ)))).MeasurableSet'
        ((shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
          ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j)) :=
    fun j => MeasurableSpace.le_def.mp
      (le_iSup (fun j : Fin (2 * m + 1) => Bsig t P ((j : ℤ) - (m : ℤ))) j) _
      (Bsig_generator_mem t P _ _)
  rw [show (winPart t P m).parts i = ⋂ j : Fin (2 * m + 1),
      (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
        ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j) from rfl]
  exact @MeasurableSet.iInter X3 (Fin (2 * m + 1))
    (⨆ j : Fin (2 * m + 1), Bsig t P ((j : ℤ) - (m : ℤ))) _
    (fun j => (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts
      ((finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)).symm i j)) hf

theorem le_partSigma_winPart (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    (⨆ j : Fin (2 * m + 1), Bsig t P ((j : ℤ) - (m : ℤ))) ≤ partSigma (winPart t P m) := by
  refine iSup_le fun j₀ => ?_
  rw [Bsig, partSigma_eq_generateFrom, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨c, ⟨i₀, rfl⟩, rfl⟩
  exact generator_mem_partSigma_winPart t P m j₀ i₀

/-- **The σ-algebra of the two-sided window is the join of the shifts.** -/
theorem partSigma_winPart (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    partSigma (winPart t P m) = ⨆ j : Fin (2 * m + 1), Bsig t P ((j : ℤ) - (m : ℤ)) :=
  le_antisymm (partSigma_winPart_le t P m) (le_partSigma_winPart t P m)


/-- The "past" σ-algebra of a partition for the map `shiftZ t 1`. -/
def pastSig (t : Fin 3 → ℝ) (R : FinPart X3) : MeasurableSpace X3 :=
  ⨆ n : ℕ, MeasurableSpace.comap ((shiftZ t 1)^[n+1]) (partSigma R)

theorem hPart_eq_Hcond_pastSig {ν : Measure X3} [IsProbabilityMeasure ν] (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (shiftZ t 1) ν ν) (R : FinPart X3) :
    hPart ν (shiftZ t 1) R = Hcond ν R (pastSig t R) :=
  hPart_Hcond ν (shiftZ t 1) (measurable_shiftZ t 1) hmp R


/-! ## The window σ-algebras `Awin` and their joins -/

/-- The join of the shifts `Bsig t P k` over `|k| ≤ m`, indexed by the subtype. -/
def Awin (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) : MeasurableSpace X3 :=
  ⨆ k : {k : ℤ // -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ)}, Bsig t P k.1

theorem Awin_mono (t : Fin 3 → ℝ) (P : FinPart X3) : Monotone (fun m : ℕ => Awin t P m) := by
  intro m m' hmm'
  unfold Awin
  refine iSup_le fun k => ?_
  have h3 : (m : ℤ) ≤ (m' : ℤ) := by exact_mod_cast hmm'
  refine le_iSup (fun k' : {k : ℤ // -(m' : ℤ) ≤ k ∧ k ≤ (m' : ℤ)} => Bsig t P k'.1)
    ⟨k.1, ?_⟩
  exact ⟨by omega, by omega⟩

theorem partSigma_winPart_le_Awin (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    partSigma (winPart t P m) ≤ Awin t P m := by
  rw [partSigma_winPart]
  refine iSup_le fun j => ?_
  have hj : (j : ℤ) < 2 * m + 1 := by exact_mod_cast j.2
  unfold Awin
  refine le_iSup (fun k' : {k : ℤ // -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ)} => Bsig t P k'.1)
    ⟨(j : ℤ) - (m : ℤ), ?_⟩
  constructor <;> omega

theorem Awin_le_partSigma_winPart (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    Awin t P m ≤ partSigma (winPart t P m) := by
  unfold Awin
  refine iSup_le fun k => ?_
  rw [partSigma_winPart]
  have hk1 : (-(m : ℤ) ≤ k.1) := k.2.1
  have hk2 : (k.1 ≤ (m : ℤ)) := k.2.2
  have hnn : (0:ℤ) ≤ k.1 + m := by omega
  have hle : k.1 + (m : ℤ) ≤ 2 * (m : ℤ) := by omega
  have hlt : (k.1 + (m : ℤ)).toNat < 2 * m + 1 := by
    have h5 : (k.1 + (m : ℤ)).toNat ≤ (2 * (m : ℤ)).toNat := Int.toNat_le.mpr hle
    have h6 : (2 * (m : ℤ)).toNat = 2 * m := by
      have : (2 * (m : ℤ)) = ((2 * m : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    omega
  have hcast : (((k.1 + (m : ℤ)).toNat : ℕ) : ℤ) = k.1 + (m : ℤ) := Int.toNat_of_nonneg hnn
  have hidx : (((⟨(k.1 + (m : ℤ)).toNat, hlt⟩ : Fin (2 * m + 1)) : ℕ) : ℤ) - (m : ℤ) = k.1 := by
    simp only [Fin.val_mk]
    rw [hcast]; ring
  rw [← hidx]
  exact le_iSup (fun j : Fin (2 * m + 1) => Bsig t P ((j : ℤ) - (m : ℤ)))
    ⟨(k.1 + (m : ℤ)).toNat, hlt⟩

theorem partSigma_winPart_eq_Awin (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    partSigma (winPart t P m) = Awin t P m :=
  le_antisymm (partSigma_winPart_le_Awin t P m) (Awin_le_partSigma_winPart t P m)

theorem iSup_Awin (t : Fin 3 → ℝ) (P : FinPart X3) :
    (⨆ m : ℕ, Awin t P m) = orbitSigma t P := by
  refine le_antisymm (iSup_le fun m => ?_) ?_
  · unfold Awin
    rw [orbitSigma]
    refine iSup_le fun k => ?_
    exact le_iSup (fun n : ℤ => MeasurableSpace.comap (fun x : X3 => aZ t n • x) (partSigma P)) k.1
  · rw [orbitSigma]
    refine iSup_le fun n => ?_
    set m : ℕ := n.natAbs with hm
    have hnat : (n.natAbs : ℤ) = if 0 ≤ n then n else -n := by
      by_cases h : 0 ≤ n
      · rw [if_pos h]; exact Int.natAbs_of_nonneg h
      · rw [if_neg h]
        have h3 : ((-n).natAbs : ℤ) = -n := Int.natAbs_of_nonneg (by omega)
        rwa [Int.natAbs_neg] at h3
    have hn1 : n ≤ (m : ℤ) := by
      rw [hm]; rw [hnat]; split <;> omega
    have hn2 : -(m : ℤ) ≤ n := by
      rw [hm]; rw [hnat]; split <;> omega
    refine le_trans (le_iSup (fun k : {k : ℤ // -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ)} =>
      Bsig t P k.1) ⟨n, hn2, hn1⟩) ?_
    exact le_iSup (fun m : ℕ => Awin t P m) m

theorem partSigma_winPart_mono (t : Fin 3 → ℝ) (P : FinPart X3) :
    Monotone (fun m : ℕ => partSigma (winPart t P m)) := by
  intro m m' h
  show partSigma (winPart t P m) ≤ partSigma (winPart t P m')
  rw [partSigma_winPart_eq_Awin, partSigma_winPart_eq_Awin]
  exact Awin_mono t P h

theorem iSup_partSigma_winPart (t : Fin 3 → ℝ) (P : FinPart X3) :
    (⨆ m : ℕ, partSigma (winPart t P m)) = orbitSigma t P := by
  rw [show (fun m : ℕ => partSigma (winPart t P m)) = fun m => Awin t P m from
    funext fun m => partSigma_winPart_eq_Awin t P m]
  exact iSup_Awin t P


/-! ## The σ-algebras `Cwin` used in the assembly -/

theorem partSigma_le_ambient (R : FinPart X3) : partSigma R ≤ instMeasurableSpaceX3 := by
  rw [partSigma_eq_generateFrom]
  exact MeasurableSpace.generateFrom_le (fun s hs => by
    rcases hs with ⟨i, rfl⟩; exact R.measurable i)

theorem orbitSigma_le_ambient (t : Fin 3 → ℝ) (P : FinPart X3) :
    orbitSigma t P ≤ instMeasurableSpaceX3 := by
  rw [orbitSigma]
  refine iSup_le fun n => ?_
  exact le_trans (MeasurableSpace.comap_mono (partSigma_le_ambient P))
    (Measurable.comap_le (by fun_prop))

theorem pastSig_le_ambient (t : Fin 3 → ℝ) (R : FinPart X3) :
    pastSig t R ≤ instMeasurableSpaceX3 := by
  unfold pastSig
  refine iSup_le fun n => ?_
  exact le_trans (MeasurableSpace.comap_mono (partSigma_le_ambient R))
    (Measurable.comap_le ((measurable_shiftZ t 1).iterate (n+1)))

theorem Awin_le_orbitSigma (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    Awin t P m ≤ orbitSigma t P := by
  unfold Awin
  rw [orbitSigma]
  refine iSup_le fun k => ?_
  exact le_iSup (fun n : ℤ => MeasurableSpace.comap (fun x : X3 => aZ t n • x) (partSigma P)) k.1

/-- `Cwin t P Q m` is the σ-algebra appearing in the chain-rule step of the assembly. -/
def Cwin (t : Fin 3 → ℝ) (P Q : FinPart X3) (m : ℕ) : MeasurableSpace X3 :=
  pastSig t (joinPart__USCBasic (winPart t P m) Q) ⊔ partSigma (winPart t P m)

theorem Cwin_le (t : Fin 3 → ℝ) (P Q : FinPart X3) (m : ℕ) :
    Cwin t P Q m ≤ instMeasurableSpaceX3 := by
  unfold Cwin
  refine sup_le (pastSig_le_ambient t _) ?_
  exact le_trans (partSigma_winPart_eq_Awin t P m).le
    (le_trans (Awin_le_orbitSigma t P m) (orbitSigma_le_ambient t P))

theorem Cwin_mono (t : Fin 3 → ℝ) (P Q : FinPart X3) : Monotone (fun m => Cwin t P Q m) := by
  intro m m' h
  unfold Cwin
  refine sup_le_sup ?_ (partSigma_winPart_mono t P h)
  refine iSup_le fun n => ?_
  have hpart : partSigma (joinPart__USCBasic (winPart t P m) Q) ≤ partSigma (joinPart__USCBasic (winPart t P m') Q) := by
    rw [partSigma_joinPart, partSigma_joinPart]
    exact sup_le_sup (partSigma_winPart_mono t P h) le_rfl
  exact le_trans (MeasurableSpace.comap_mono hpart)
    (le_iSup (fun n' : ℕ => MeasurableSpace.comap ((shiftZ t 1)^[n'+1])
      (partSigma (joinPart__USCBasic (winPart t P m') Q))) n)

theorem le_iSup_Cwin (t : Fin 3 → ℝ) (P Q : FinPart X3) :
    orbitSigma t P ⊔ pastSig t Q ≤ ⨆ m, Cwin t P Q m := by
  apply sup_le
  · rw [orbitSigma]
    refine iSup_le fun k => ?_
    set m : ℕ := k.natAbs with hm
    have hnat : (k.natAbs : ℤ) = if 0 ≤ k then k else -k := by
      by_cases h : 0 ≤ k
      · rw [if_pos h]; exact Int.natAbs_of_nonneg h
      · rw [if_neg h]
        have h3 : ((-k).natAbs : ℤ) = -k := Int.natAbs_of_nonneg (by omega)
        rwa [Int.natAbs_neg] at h3
    have hn1 : k ≤ (m : ℤ) := by rw [hm]; rw [hnat]; split <;> omega
    have hn2 : -(m : ℤ) ≤ k := by rw [hm]; rw [hnat]; split <;> omega
    refine le_trans ?_ (le_iSup (fun m => Cwin t P Q m) m)
    refine le_trans ?_ (le_sup_right : partSigma (winPart t P m) ≤ Cwin t P Q m)
    refine le_trans ?_ (Awin_le_partSigma_winPart t P m)
    unfold Awin
    exact le_iSup (fun k' : {k : ℤ // -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ)} => Bsig t P k'.1)
      ⟨k, hn2, hn1⟩
  · have h1 : partSigma Q ≤ partSigma (joinPart__USCBasic (winPart t P 0) Q) := by
      rw [partSigma_joinPart]; exact le_sup_right
    have h2 : pastSig t Q ≤ pastSig t (joinPart__USCBasic (winPart t P 0) Q) := by
      unfold pastSig
      refine iSup_le fun n => ?_
      exact le_trans (MeasurableSpace.comap_mono h1)
        (le_iSup (fun n' : ℕ => MeasurableSpace.comap ((shiftZ t 1)^[n'+1])
          (partSigma (joinPart__USCBasic (winPart t P 0) Q))) n)
    exact le_trans (le_trans h2 le_sup_left) (le_iSup (fun m => Cwin t P Q m) 0)

end Work.EKLComp
