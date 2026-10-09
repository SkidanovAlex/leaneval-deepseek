import Mathlib
import Submission.Work.SSGRoute.H9.swHistK
import Submission.Work.SSGRoute.H9.escape_realisation_core_normalised
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.H9.swHistDatum_add
import Submission.Work.SSGRoute.H9.swHistDatum_locConst
import Submission.Work.SSGRoute.H9.swHistDatum_gesKConj_congr
import Submission.Work.SSGRoute.H9.swHistDatum_conj_inv
import Submission.Work.SSGRoute.H9.swHistPlacesK_isFinPlace
import Submission.Work.SSGRoute.H9.swHistPlacesK_covers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Existence of the Kummer-form history of the Schmidt--Wingberg §4 recursion

This file proves `Work.SSGRoute.H9.swHistKExists_proved`: the recursion whose one-stage step is the
escape oracle `Work.SSGRoute.H9.escape_realisation_core_normalised`, applied at stage `m` with the
place set `T_m = histPlacesK ... m f`, the global datum `g = ½y` and the local datum
`h = histDatumK ... m f`.

## The shape of the argument

1. `Pre n f` is the history predicate `HistK` with every `∀ m : ℕ` replaced by `∀ m < n`;
   `HistK` itself is recovered from `∀ n, Pre n f`.
2. `Pre_step` is the one-stage step: it produces a new escape prime `Q` and element `b` such that
   `Pre (n+1) (Function.update f n (Q, b))`.
3. The step applies the oracle to the *system of `K`-class representatives* `krep K T_m` of `T_m`
   (`krep` picks one element per `gesKConj K`-class met by `T_m`), which is pairwise
   non-`K`-conjugate — unlike `T_m = histPlacesK`, whose elements `galLift K σ • A` may be
   `K`-conjugate when the `k`-place of `A` is not split in `K`.  The oracle's conclusion is
   transported back to all of `T_m` using the `K`-conjugacy invariance of the Kummer cochains, of
   `½y` and of `histDatumK`.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-! ## Elementary bookkeeping -/

/-- An additive function on a subgroup kills the unit. -/
theorem swAdd_one_eq_zero {Γ M : Type} [Group Γ] [AddCommGroup M] {H : Subgroup Γ}
    {f : Γ → M} (hf : ∀ x ∈ H, ∀ y ∈ H, f (x * y) = f x + f y) : f 1 = 0 := by
  have h := hf 1 H.one_mem 1 H.one_mem
  rw [one_mul] at h
  have h' : f 1 + 0 = f 1 + f 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

theorem swNodeKummerCocharZMod_one (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b 1 = 0 :=
  swAdd_one_eq_zero (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b)

/-- Level-`K` conjugacy of places is transitive. -/
theorem swGesKConj_trans {K : IntermediateField k Ω} {A B C : ValuationSubring Ω}
    (h₁ : Work.SSGRoute.gesKConj K A B) (h₂ : Work.SSGRoute.gesKConj K B C) :
    Work.SSGRoute.gesKConj K A C := by
  obtain ⟨τ, hτ, hτA⟩ := h₁
  obtain ⟨υ, hυ, hυB⟩ := h₂
  exact ⟨υ * τ, K.fixingSubgroup.mul_mem hυ hτ, by rw [mul_smul, hτA, hυB]⟩

/-- Level-`K` conjugacy of places is symmetric. -/
theorem swGesKConj_symm {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) : Work.SSGRoute.gesKConj K B A := by
  obtain ⟨τ, hτ, hτA⟩ := h
  exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, by rw [← hτA, inv_smul_smul]⟩

/-! ## The system of `K`-class representatives `krep` -/

/-- The setoid of level-`K` conjugacy of places. -/
noncomputable def gesKConjSetoid (K : IntermediateField k Ω) : Setoid (ValuationSubring Ω) where
  r := Work.SSGRoute.gesKConj K
  iseqv :=
    ⟨fun A => ⟨1, K.fixingSubgroup.one_mem, one_smul _ _⟩,
      fun h => by
        obtain ⟨τ, hτ, hτA⟩ := h
        exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, by rw [← hτA, inv_smul_smul]⟩,
      fun h₁ h₂ => swGesKConj_trans h₁ h₂⟩

/-- **One representative per `K`-class met by `T`.** -/
noncomputable def krep (K : IntermediateField k Ω) (T : Finset (ValuationSubring Ω)) :
    Finset (ValuationSubring Ω) := by
  classical
  exact (T.image (Quotient.mk (gesKConjSetoid K))).image (fun q => Quotient.out q)

theorem krep_covers (K : IntermediateField k Ω) (T : Finset (ValuationSubring Ω)) :
    ∀ A ∈ T, ∃ A' ∈ krep K T, Work.SSGRoute.gesKConj K A' A := by
  classical
  intro A hA
  set q : Quotient (gesKConjSetoid K) := Quotient.mk (gesKConjSetoid K) A with hq
  refine ⟨Quotient.out q, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨q, Finset.mem_image.mpr ⟨A, hA, rfl⟩, rfl⟩
  · exact Quotient.exact (Quotient.out_eq q)

theorem krep_mem_classes (K : IntermediateField k Ω) (T : Finset (ValuationSubring Ω)) :
    ∀ A ∈ krep K T, ∃ A' ∈ T, Work.SSGRoute.gesKConj K A A' := by
  classical
  intro A hA
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨A', hA', hA'q⟩ := Finset.mem_image.mp hq
  refine ⟨A', hA', ?_⟩
  have h : Quotient.mk (gesKConjSetoid K) (Quotient.out q)
      = Quotient.mk (gesKConjSetoid K) A' := by
    rw [hA'q]; exact Quotient.out_eq q
  exact @Quotient.exact _ (gesKConjSetoid K) _ _ h

theorem krep_disj (K : IntermediateField k Ω) (T : Finset (ValuationSubring Ω)) :
    ∀ A ∈ krep K T, ∀ B ∈ krep K T, Work.SSGRoute.gesKConj K A B → A = B := by
  classical
  intro A hA B hB hAB
  obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨q₂, hq₂, rfl⟩ := Finset.mem_image.mp hB
  have h : Quotient.mk (gesKConjSetoid K) (Quotient.out q₁)
      = Quotient.mk (gesKConjSetoid K) (Quotient.out q₂) :=
    @Quotient.sound _ (gesKConjSetoid K) _ _ hAB
  rw [Quotient.out_eq q₁, Quotient.out_eq q₂] at h
  rw [h]

/-! ## The place set `histPlacesK` and the datum `histDatumK` -/

/-- **The membership cases of `histPlacesK`**: a block is `k`-conjugate to `S` or to an escape
prime of the prefix. -/
theorem mem_histPlacesK_cases {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {S : Finset (ValuationSubring Ω)} {ζ : Ω} {hζK : ζ ∈ K} {hζ : IsPrimitiveRoot ζ p}
    {m : ℕ} {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {A : ValuationSubring Ω}
    (hA : A ∈ histPlacesK (p := p) K S ζ hζK hζ m f) :
    (∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) ∨
      (∃ l : ℕ, l < m ∧ SSGRoute.IsConjPlace k ((f l).1) A) := by
  classical
  simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, histClass, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_univ, true_and] at hA
  rcases hA with hA | ⟨l, hA⟩
  · exact Or.inl (Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := p) K hA)
  · obtain ⟨A₀, hA₀, hc⟩ := Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := p) K hA
    rw [Finset.mem_singleton] at hA₀
    subst hA₀
    exact Or.inr ⟨l.1, l.2, hc⟩

theorem histPlacesK_congr {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {S : Finset (ValuationSubring Ω)} {ζ : Ω} {hζK : ζ ∈ K} {hζ : IsPrimitiveRoot ζ p}
    {m : ℕ} {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} (h : ∀ i < m, f i = g i) :
    histPlacesK (p := p) K S ζ hζK hζ m f = histPlacesK (p := p) K S ζ hζK hζ m g := by
  have hfun : (fun j : Fin m => f j) = (fun j : Fin m => g j) := funext fun i => h i i.2
  simp only [histPlacesK, hfun]

theorem histDatumK_congr {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {S : Finset (ValuationSubring Ω)} {ζ : Ω} {hζK : ζ ∈ K} {hζ : IsPrimitiveRoot ζ p}
    {y : (Ω ≃ₐ[k] Ω) → ZMod p} {m : ℕ} {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    (h : ∀ i < m, f i = g i) :
    histDatumK (p := p) K ζ hζK hζ S y m f = histDatumK (p := p) K ζ hζK hζ S y m g := by
  have hfun : (fun j : Fin m => f j) = (fun j : Fin m => g j) := funext fun i => h i i.2
  simp only [histDatumK, hfun]

/-- **The accumulated datum of a history vanishes at a block that is `k`-conjugate to no escape
prime of the history.** -/
theorem swHistDatum_eq_zero_of_forall_not_conjPlace (K : IntermediateField k Ω)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    {n : ℕ} (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (A : ValuationSubring Ω)
    (h : ∀ j, ¬ SSGRoute.IsConjPlace k ((f j).1) A) :
    Work.SSGRoute.ZDataMup.histDatum K y f A = 0 := by
  funext τ
  simp only [Work.SSGRoute.ZDataMup.histDatum]
  exact Finset.sum_eq_zero fun j _ => congrFun
    (Work.SSGRoute.ZDataMup.correctionDatum_eq_zero_of_not_conjPlace K
      (fun σ => (2 : ZMod p)⁻¹ * y σ) ((f j).2) ((f j).1) A (h j)) τ

/-! ## The prefix predicate `Pre` -/

/-- **The prefix form of the Kummer-form invariant.**  This is `HistK` with each `∀ m : ℕ` replaced
by `∀ m < n` (the place set and datum of stage `m` being those of the prefix). -/
def Pre (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p) (n : ℕ)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) : Prop :=
  (∀ m < n, SSGRoute.IsFinPlace k ((f m).1)) ∧
  (∀ m < n, SSGRoute.IsSplitIn k N ((f m).1)) ∧
  (∀ m l : ℕ, m < l → l < n → ¬ Work.SSGRoute.gesKConj K ((f m).1) ((f l).1)) ∧
  (∀ m < n, ∀ A ∈ histPlacesK (p := p) K S ζ hζK hζ m f,
      ¬ Work.SSGRoute.gesKConj K A ((f m).1)) ∧
  (∀ m < n, ∀ A ∈ histPlacesK (p := p) K S ζ hζK hζ m f,
      ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 σ =
          (2 : ZMod p)⁻¹ * y σ + histDatumK (p := p) K ζ hζK hζ S y m f A σ) ∧
  (∀ m < n, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ histPlacesK (p := p) K S ζ hζK hζ m f, ¬ Work.SSGRoute.gesKConj K A B) →
      (¬ Work.SSGRoute.gesKConj K ((f m).1) B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 σ = 0) ∧
  (∀ m < n, ∃ u : (↥K)ˣ,
      (∃ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        ((f m).1).comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
        FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (u : ↥K)) = 1) ∧
      (∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k ((f m).1) →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ ((f m).2 * u) σ = 0))

/-- `Pre` depends only on the first `n` values of `f`. -/
theorem Pre_congr {K N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] {ζ : Ω} {hζ : IsPrimitiveRoot ζ p} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod p} {n : ℕ}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} (h : ∀ i < n, f i = g i)
    (hf : Pre (p := p) K N ζ hζ hζK S y n f) :
    Pre (p := p) K N ζ hζ hζK S y n g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
  have hp := fun m hm => histPlacesK_congr (p := p) (K := K) (S := S) (ζ := ζ) (hζK := hζK)
    (hζ := hζ) (m := m) (f := f) (g := g) fun i hi => h i (lt_trans hi hm)
  have hd := fun m hm => histDatumK_congr (p := p) (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
    (S := S) (y := y) (m := m) (f := f) (g := g) fun i hi => h i (lt_trans hi hm)
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m l hml hl => ?_, fun m hm => ?_, fun m hm => ?_,
    fun m hm => ?_, fun m hm => ?_⟩
  · rw [← h m hm]; exact h1 m hm
  · rw [← h m hm]; exact h2 m hm
  · rw [← h m (lt_trans hml hl), ← h l hl]; exact h3 m l hml hl
  · rw [← hp m hm, ← h m hm]; exact h4 m hm
  · rw [← hp m hm, ← hd m hm, ← h m hm]; exact h5 m hm
  · rw [← hp m hm, ← h m hm]; exact h6 m hm
  · rw [← h m hm]; exact h7 m hm

/-! ## `HistK` from `Pre` -/

theorem histK_of_all_Pre {K N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] {ζ : Ω} {hζ : IsPrimitiveRoot ζ p} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod p}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} (hf : ∀ n, Pre (p := p) K N ζ hζ hζK S y n f) :
    HistK (p := p) K N ζ hζ hζK S y f := by
  refine ⟨fun m => ?_, fun m => ?_, fun m l hml => ?_, fun m => ?_, fun m => ?_, fun m => ?_,
    fun m => ?_⟩
  · exact (hf (m + 1)).1 m (Nat.lt_succ_self m)
  · exact (hf (m + 1)).2.1 m (Nat.lt_succ_self m)
  · exact (hf (l + 1)).2.2.1 m l hml (Nat.lt_succ_self l)
  · exact (hf (m + 1)).2.2.2.1 m (Nat.lt_succ_self m)
  · exact (hf (m + 1)).2.2.2.2.1 m (Nat.lt_succ_self m)
  · exact (hf (m + 1)).2.2.2.2.2.1 m (Nat.lt_succ_self m)
  · exact (hf (m + 1)).2.2.2.2.2.2 m (Nat.lt_succ_self m)

/-! ## The recursion step -/

theorem Pre_step (hp : p ≠ 2) {K N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    {ζ : Ω} {hζ : IsPrimitiveRoot ζ p} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    {y : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    {n : ℕ} {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    (hf : Pre (p := p) K N ζ hζ hζK S y n f) :
    ∃ x : ValuationSubring Ω × (↥K)ˣ,
      Pre (p := p) K N ζ hζ hζK S y (n + 1) (Function.update f n x) := by
  classical
  obtain ⟨hfin, hsplit, hdisj, hexcl, hreal, hconf, hnorm⟩ := hf
  -- the global datum
  set g : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => (2 : ZMod p)⁻¹ * y σ with hgdef
  have hgadd : ∀ x ∈ K.fixingSubgroup, ∀ z ∈ K.fixingSubgroup, g (x * z) = g x + g z := by
    intro x hx z hz
    simp only [hgdef, hy x hx z hz]
    ring
  have hgloc : SSGRoute.IsLocConstOn K.fixingSubgroup g := by
    obtain ⟨U, hUo, hU⟩ := hyc
    exact ⟨U, hUo, fun a ha u hu huH => by
      simp only [hgdef]
      rw [hU a ha u hu huH]⟩
  have hy1 : y 1 = 0 := swAdd_one_eq_zero hy
  -- the place set and the datum
  set T : Finset (ValuationSubring Ω) := histPlacesK (p := p) K S ζ hζK hζ n f with hTdef
  set T'' : Finset (ValuationSubring Ω) := krep K T with hT''def
  set h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p :=
    histDatumK (p := p) K ζ hζK hζ S y n f with hhdef
  -- the oracle hypotheses
  have hT''fin : ∀ A ∈ T'', SSGRoute.IsFinPlace k A := by
    intro A hA
    obtain ⟨A', hA', hA'A⟩ := krep_mem_classes K T A hA
    have hA'fin : SSGRoute.IsFinPlace k A' :=
      swHistPlacesK_isFinPlace (p := p) K S ζ hζK hζ f n hSfin (fun j hj => hfin j hj) A' hA'
    obtain ⟨τ, hτ, hτA⟩ := hA'A
    rw [← hτA] at hA'fin
    exact (Work.SSGRoute.isFinPlace_smul_iff A τ).mp hA'fin
  have hT''cov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T'', Work.SSGRoute.gesKConj K A B := by
    intro B hB hcond
    have hram : SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1 := by
      rcases hcond with h | ⟨σ, -, hσI, hσN⟩
      · exact Or.inr h
      · exact Or.inl ⟨σ, hσI, hσN⟩
    obtain ⟨A₀, hA₀, hA₀B⟩ := hSram B hB hram
    obtain ⟨A', hA', hA'B⟩ :=
      swHistPlacesK_covers (p := p) K S ζ hζK hζ f n (Or.inl ⟨A₀, hA₀, hA₀B⟩)
    obtain ⟨A'', hA'', hA''A'⟩ := krep_covers K T A' hA'
    exact ⟨A'', hA'', swGesKConj_trans hA''A' hA'B⟩
  have hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T'', ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0 := by
    intro B hB hBT hns σ hσK hσI
    have hBS : ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ B := by
      intro A₀ hA₀ hconj
      obtain ⟨A', hA', hA'B⟩ :=
        swHistPlacesK_covers (p := p) K S ζ hζK hζ f n (Or.inl ⟨A₀, hA₀, hconj⟩)
      obtain ⟨A'', hA'', hA''A'⟩ := krep_covers K T A' hA'
      exact hBT A'' hA'' (swGesKConj_trans hA''A' hA'B)
    have hy0 : y σ = 0 := hyS B hB hBS hns σ hσK hσI
    simp only [hgdef, hy0, mul_zero]
  have hh : ∀ A ∈ T'', ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ z ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * z) = h A x + h A z := by
    intro A _ x hx z hz
    exact swHistDatum_add (p := p) K y hy
      (histClass (p := p) K ζ hζK hζ (fun j : Fin n => f j))
      (fun j => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (f j).2) A x hx z hz
  have hhc : ∀ A ∈ T'', ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0 := by
    intro A _
    exact swHistDatum_locConst (p := p) K y hy1 hyc
      (histClass (p := p) K ζ hζK hζ (fun j : Fin n => f j))
      (fun j => by
        simpa only [histClass] using swNodeKummerCocharZMod_one K ζ hζ hζK (f j).2)
      (fun j => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ (f j).2) A
  have hnormN : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  have horth : ∀ A ∈ T'', (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      SSGRoute.IsSplitIn k N A := by
    intro A hA
    obtain ⟨A₀, hA₀, hA₀A⟩ := krep_mem_classes K T A hA
    rcases mem_histPlacesK_cases (p := p) (K := K) (S := S) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (f := f) (m := n) hA₀ with hS' | ⟨l, hln, hlA₀⟩
    · left
      have hAA₀ : h A = h A₀ :=
        swHistDatum_gesKConj_congr (p := p) K y
          (histClass (p := p) K ζ hζK hζ (fun j : Fin n => f j)) A A₀ hA₀A
      have h0 : h A₀ = 0 := by
        refine swHistDatum_eq_zero_of_forall_not_conjPlace K y
          (histClass (p := p) K ζ hζK hζ (fun j : Fin n => f j)) A₀ fun j hconj => ?_
        obtain ⟨A₁, hA₁, hA₁A₀⟩ := hS'
        have hA₁Q : SSGRoute.IsConjPlace k A₁ ((f j).1) :=
          SSGRoute.isConjPlace_trans hA₁A₀ (SSGRoute.isConjPlace_symm hconj)
        obtain ⟨A', hA', hA'Q⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA₁ hA₁Q
        have hA'mem : A' ∈ histPlacesK (p := p) K S ζ hζK hζ (j : ℕ) f := by
          simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, Finset.mem_union]
          exact Or.inl hA'
        exact hexcl (j : ℕ) j.2 A' hA'mem hA'Q
      intro σ _
      rw [hAA₀]
      exact congrFun h0 σ
    · right
      obtain ⟨ρ, hρ⟩ := hlA₀
      obtain ⟨τ, hτK, hτA⟩ := hA₀A
      have hkey : (τ⁻¹ * ρ) • (f l).1 = A := by
        rw [mul_smul, hρ, ← hτA, inv_smul_smul]
      rw [← hkey]
      exact (Work.SSGRoute.isSplitIn_conj N hnormN ((f l).1) (τ⁻¹ * ρ)).mpr (hsplit l hln)
  -- the oracle
  obtain ⟨z', Q', b, hQ'fin, hQ'split, hQ'notT, hz'add, hz'loc, hz'presc, hz'unr, hz'kum,
    hnorm'⟩ :=
    escape_realisation_core_normalised p hp k Ω K N hKN ζ hζ hζK T'' hT''fin
      (fun A hA B hB hconj => krep_disj K T A hA B hB hconj) hT''cov g hgadd hgloc hgram h hh hhc
      horth
  refine ⟨(Q', b), ?_⟩
  -- the new prefix
  have hupd : ∀ i < n, Function.update f n (Q', b) i = f i := by
    intro i hi
    rw [Function.update_of_ne]
    omega
  have hupd_n : Function.update f n (Q', b) n = (Q', b) := by
    rw [Function.update_apply, if_pos rfl]
  have hTcongr : ∀ m ≤ n, histPlacesK (p := p) K S ζ hζK hζ m (Function.update f n (Q', b))
      = histPlacesK (p := p) K S ζ hζK hζ m f := by
    intro m hm
    exact histPlacesK_congr (p := p) (K := K) (S := S) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (f := Function.update f n (Q', b)) (g := f) fun i hi => hupd i (lt_of_lt_of_le hi hm)
  have hDcongr : ∀ m ≤ n, histDatumK (p := p) K ζ hζK hζ S y m (Function.update f n (Q', b))
      = histDatumK (p := p) K ζ hζK hζ S y m f := by
    intro m hm
    exact histDatumK_congr (p := p) (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (S := S)
      (y := y) (f := Function.update f n (Q', b)) (g := f) fun i hi => hupd i (lt_of_lt_of_le hi hm)
  -- an element of `T''` that is `K`-conjugate to `(f m).1`
  have hmemQ : ∀ m < n, ∃ A ∈ T'', Work.SSGRoute.gesKConj K A ((f m).1) := by
    intro m hm
    obtain ⟨A', hA', hA'Q⟩ := swHistPlacesK_covers (p := p) K S ζ hζK hζ f n
      (Or.inr ⟨⟨m, hm⟩, ⟨1, one_smul _ _⟩⟩)
    obtain ⟨A'', hA'', hA''A'⟩ := krep_covers K T A' hA'
    exact ⟨A'', hA'', swGesKConj_trans hA''A' hA'Q⟩
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m l hml hl => ?_, fun m hm => ?_, fun m hm => ?_,
    fun m hm => ?_, fun m hm => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | heq
    · rw [hupd m hm']; exact hfin m hm'
    · rw [heq, hupd_n]; exact hQ'fin
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | heq
    · rw [hupd m hm']; exact hsplit m hm'
    · rw [heq, hupd_n]; exact hQ'split
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | heq
    · rw [hupd m (lt_trans hml hl'), hupd l hl']; exact hdisj m l hml hl'
    · have hmn : m < n := heq ▸ hml
      rw [heq, hupd m hmn, hupd_n]
      obtain ⟨A, hA, hAQ⟩ := hmemQ m hmn
      exact fun hconj => hQ'notT A hA (swGesKConj_trans hAQ hconj)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | heq
    · rw [hTcongr m (le_of_lt hm'), hupd m hm']; exact hexcl m hm'
    · rw [heq, hTcongr n le_rfl, hupd_n]
      intro A hA
      obtain ⟨A'', hA'', hA''A⟩ := krep_covers K T A hA
      exact fun hconj => hQ'notT A'' hA'' (swGesKConj_trans hA''A hconj)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | heq
    · rw [hTcongr m (le_of_lt hm'), hDcongr m (le_of_lt hm'), hupd m hm']; exact hreal m hm'
    · rw [heq, hTcongr n le_rfl, hDcongr n le_rfl, hupd_n]
      intro A hA σ hσ
      obtain ⟨A'', hA'', τ, hτK, hτA⟩ := krep_covers K T A hA
      set σ'' : Ω ≃ₐ[k] Ω := τ⁻¹ * σ * τ with hσ''def
      have hσ''K : σ'' ∈ K.fixingSubgroup :=
        K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hτK) hσ.2) hτK
      have hσ''A : σ'' ∈ SSGRoute.decomp k A'' ⊓ K.fixingSubgroup := by
        refine Subgroup.mem_inf.mpr ⟨?_, hσ''K⟩
        show σ'' • A'' = A''
        rw [hσ''def, mul_smul, mul_smul, hτA, (hσ.1 : σ • A = A), ← hτA, inv_smul_smul]
      have hconjσ : τ * σ'' * τ⁻¹ = σ := by rw [hσ''def]; group
      have horacle : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ''
          = g σ'' + h A'' σ'' := by
        have h := hz'presc A'' hA'' σ'' hσ''A
        rw [hz'kum σ'' hσ''K] at h
        exact h
      have hchi : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ
          = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ'' := by
        rw [← hconjσ]
        exact Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK b hτK σ''
      have hgσ : g σ'' = g σ := by
        have h := Work.SSGRoute.ZDataMup.additive_conj_invariant K y hy hτK hσ''K
        simp only [hgdef]
        rw [← h, hconjσ]
      have hhd : h A'' σ'' = h A σ := by
        have h1 : h A'' = h A :=
          swHistDatum_gesKConj_congr (p := p) K y
            (histClass (p := p) K ζ hζK hζ (fun j : Fin n => f j)) A'' A ⟨τ, hτK, hτA⟩
        have h2 : h A (τ * σ'' * τ⁻¹) = h A σ'' :=
          swHistDatum_conj_inv (p := p) K y
            (histClass (p := p) K ζ hζK hζ (fun j : Fin n => f j)) A τ σ'' hτK hσ''K
            (fun s hs => Work.SSGRoute.ZDataMup.additive_conj_invariant K y hy hτK hs)
            (fun j s hs =>
              Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (f j).2 hτK s)
        rw [h1, ← h2, hconjσ]
      rw [hchi, horacle, hgσ, hhd]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | heq
    · rw [hTcongr m (le_of_lt hm'), hupd m hm']; exact hconf m hm'
    · rw [heq, hTcongr n le_rfl, hupd_n]
      intro B hB hBT hQB σ hσK hσI
      have hBT' : ∀ A ∈ T'', ¬ Work.SSGRoute.gesKConj K A B := by
        intro A hA hconj
        obtain ⟨A', hA', hA'A⟩ := krep_mem_classes K T A hA
        exact hBT A' hA' (swGesKConj_trans (swGesKConj_symm hA'A) hconj)
      have hz0 : z' σ = 0 := hz'unr B hB hBT' hQB σ hσK hσI
      rw [← hz'kum σ hσK]
      exact hz0
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | heq
    · rw [hupd m hm']; exact hnorm m hm'
    · rw [heq, hupd_n]; exact hnorm'

/-! ## The theorem -/

/-- **The Kummer-form recursion of Schmidt–Wingberg §4 exists.**  A history `f : ℕ → (Q_m, b_m)`
of escape primes with elements, satisfying the `HistK` invariants of
`Submission/Work/SSGRoute/H9/swHistK.lean`: each `Q_m` is finite, split in `N`, pairwise
non-`K`-conjugate and outside the blocks of its own place set `T_m = histPlacesK K S ζ hζK hζ m f`;
the Kummer cochains `χ_{b_m}` realise the prescribed total `½y + histDatumK` on the local groups of
the blocks of `T_m`, kill the inertia outside `cs(T_m) ∪ cs(Q_m)`, and satisfy the escape
normalisation `v_{Q_m}(b_m) ≡ −1 (mod p)`. -/
theorem swHistKExists_proved {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) :
    ∃ f : ℕ → (ValuationSubring Ω × (↥K)ˣ),
      Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f := by
  classical
  have hstep : ∀ (n : ℕ) (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)),
      Pre (p := p) K N ζ hζ hζK S y n f →
      ∃ x : ValuationSubring Ω × (↥K)ˣ,
        Pre (p := p) K N ζ hζ hζK S y (n + 1) (Function.update f n x) :=
    fun n f hf => Pre_step (p := p) hp hKN hSfin hSram hy hyc hyS hf
  have hbase : Pre (p := p) K N ζ hζ hζK S y 0
      (fun _ => (default : ValuationSubring Ω × (↥K)ˣ)) := by
    refine ⟨fun m hm => absurd hm (Nat.not_lt_zero m), fun m hm => absurd hm (Nat.not_lt_zero m),
      fun m l hml hl => absurd hl (Nat.not_lt_zero l), fun m hm => absurd hm (Nat.not_lt_zero m),
      fun m hm => absurd hm (Nat.not_lt_zero m), fun m hm => absurd hm (Nat.not_lt_zero m),
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  let seq : (n : ℕ) → {f : ℕ → (ValuationSubring Ω × (↥K)ˣ) //
      Pre (p := p) K N ζ hζ hζK S y n f} :=
    Nat.rec (motive := fun n => {f : ℕ → (ValuationSubring Ω × (↥K)ˣ) //
        Pre (p := p) K N ζ hζ hζK S y n f})
      ⟨fun _ => (default : ValuationSubring Ω × (↥K)ˣ), hbase⟩
      (fun n ih => ⟨Function.update ih.1 n (Classical.choose (hstep n ih.1 ih.2)),
        Classical.choose_spec (hstep n ih.1 ih.2)⟩)
  let F : ℕ → (ValuationSubring Ω × (↥K)ˣ) := fun m => (seq (m + 1)).1 m
  have hagree : ∀ n i, i < n → (seq n).1 i = F i := by
    intro n
    induction n with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · show (seq (n + 1)).1 i = F i
        rw [show (seq (n + 1)).1
            = Function.update (seq n).1 n
                (Classical.choose (hstep n (seq n).1 (seq n).2)) from rfl]
        rw [Function.update_of_ne (by omega : i ≠ n)]
        exact ih i hi
      · rfl
  have hPre : ∀ n, Pre (p := p) K N ζ hζ hζK S y n F := fun n =>
    Pre_congr (p := p) (K := K) (N := N) (ζ := ζ) (hζ := hζ) (hζK := hζK) (S := S) (y := y)
      (f := (seq n).1) (g := F) (fun i hi => hagree n i hi) (seq n).2
  exact ⟨F, histK_of_all_Pre (p := p) (K := K) (N := N) (ζ := ζ) (hζ := hζ) (hζK := hζK)
    (S := S) (y := y) (f := F) hPre⟩

end Work.SSGRoute.H9
