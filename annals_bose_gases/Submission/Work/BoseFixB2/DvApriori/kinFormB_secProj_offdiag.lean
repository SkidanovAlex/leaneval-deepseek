import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.fsTbil_add_left
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.kinFormB_offdiag_of_notMem
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.slotTerm_zero_of_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.kinFormB_secProj_offdiag`

FS §6 (`lem:LocMatrices`): the **kinetic** part of the box Hamiltonian is *block diagonal* in
the excitation-number grading `1_{n₊=k}`: its off-diagonal polarisation vanishes,

    `(kinFormB (sᵢΦ + sₖΦ) − kinFormB (sᵢΦ − sₖΦ))/4 = 0`   for `i ≠ k`.

**STATUS: complete** (no `sorry`; axioms `propext, Classical.choice, Quot.sound`).

Route: expand `kinFormB` (a finite sum over the `n` slots) and pull the difference into the
slot integrand; expand each slot over the joint projections `jointProj ℓ S Φ` (`S ∈ powersetCard i`,
`T ∈ powersetCard k`) using the fibre algebra and the polarisation identities; then every slot
term vanishes: when `(a:ℕ) ∈ S ∩ T` by `KinOffdiag.slotTerm_zero_of_mem` (the four kinetic words
are each quadratic, hence their polarisations are the off-diagonal expressions killed by
`*Word_fibre_offdiag`), and otherwise by `KinOffdiag.kinFormB_offdiag_of_notMem`.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary fibre algebra -/

/-- The slot fibre is additive. -/
lemma fibre_add_eq {n : ℕ} (a : Fin n) (Φ Ψ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    fibre n a (Φ + Ψ) x = fibre n a Φ x + fibre n a Ψ x := rfl

/-- The slot fibre is subtractive. -/
lemma fibre_sub_eq {n : ℕ} (a : Fin n) (Φ Ψ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    fibre n a (Φ - Ψ) x = fibre n a Φ x - fibre n a Ψ x := rfl

/-- The slot fibre of a finite sum is the finite sum of the fibres. -/
lemma fibre_finsetSum {n : ℕ} (a : Fin n) {ι : Type*} (s : Finset ι)
    (f : ι → Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    fibre n a (∑ i ∈ s, f i) x = ∑ i ∈ s, fibre n a (f i) x := by
  funext z
  simp only [fibre, Finset.sum_apply]

/-- The slot fibre of `secProj` is the sum of the fibres of the joint projections. -/
lemma fibre_secProj {n : ℕ} (a : Fin n) (ℓ : ℝ) (k : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    fibre n a (secProj ℓ k Φ) x
      = ∑ S ∈ (Finset.range n).powersetCard k, fibre n a (jointProj ℓ S Φ) x := by
  rw [secProj]
  exact fibre_finsetSum a _ _ _

/-! ## 2. Evenness of `fsT`, symmetry of `fsTbil` -/

/-- `fsT` is even in its state (no hypothesis on the state, no hypothesis on the parameters). -/
lemma fsT_fun_neg {ℓ d s εT b : ℝ} (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    fsT ℓ d s εT b 0 (fun z => - ψ z) = fsT ℓ d s εT b 0 ψ := by
  have h := Work.BoseFixB2.Polar.SmulAux.fsT_const_mul (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) (b := b) (c := (-1 : ℝ)) (0 : EuclideanSpace ℝ (Fin 3)) ψ
  have h2 : (fun z : EuclideanSpace ℝ (Fin 3) => -1 * ψ z) = (fun z => -ψ z) := by
    funext z; ring
  rw [h2] at h
  rw [h]
  ring

/-- `fsTbil` is symmetric in its two slots. -/
lemma fsTbil_symm {ℓ d s εT b : ℝ} (f g : EuclideanSpace ℝ (Fin 3) → ℝ) :
    fsTbil ℓ d s εT b 0 f g = fsTbil ℓ d s εT b 0 g f := by
  unfold Work.BoseFixB2.fsTbil
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) => g z + f z) = (fun z => f z + g z) from by funext z; ring,
    show (fun z : EuclideanSpace ℝ (Fin 3) => g z - f z) = (fun z => -(f z - g z)) from by funext z; ring,
    fsT_fun_neg]

/-! ## 3. Smoothness of finite sums of one-body states -/

/-- A finite sum of smooth scalar-valued functions on a normed space is smooth. -/
lemma contDiff_finsetSum {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : Finset ι) {u : ι → E → ℝ}
    (hu : ∀ i ∈ σ, ContDiff ℝ (⊤ : ℕ∞) (u i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ i ∈ σ, u i z) := by
  classical
  induction σ using Finset.induction_on with
  | empty => simpa using contDiff_const (c := (0 : ℝ))
  | insert a σ ha ih =>
      have ha' : ContDiff ℝ (⊤ : ℕ∞) (u a) := hu a (Finset.mem_insert_self a σ)
      have hs' : ∀ i ∈ σ, ContDiff ℝ (⊤ : ℕ∞) (u i) :=
        fun i hi => hu i (Finset.mem_insert_of_mem hi)
      simpa only [Finset.sum_insert ha, Pi.add_apply] using ha'.add (ih hs')

/-! ## 4. Finite-sum additivity of `fsTbil` -/

/-- Additivity of `fsTbil` in a finite sum in its first slot. -/
lemma fsTbil_sum_left {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {ι : Type*} (σ : Finset ι)
    {u : ι → EuclideanSpace ℝ (Fin 3) → ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ∀ i ∈ σ, ContDiff ℝ (⊤ : ℕ∞) (u i)) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    fsTbil ℓ d s εT b 0 (fun z => ∑ i ∈ σ, u i z) g
      = ∑ i ∈ σ, fsTbil ℓ d s εT b 0 (u i) g := by
  classical
  induction σ using Finset.induction_on with
  | empty =>
      have h0 : (fun z : EuclideanSpace ℝ (Fin 3) => ∑ i ∈ (∅ : Finset ι), u i z)
          = (0 : EuclideanSpace ℝ (Fin 3) → ℝ) := by
        funext z; simp
      rw [h0]
      unfold Work.BoseFixB2.fsTbil
      rw [show (fun z : EuclideanSpace ℝ (Fin 3) => (0 : EuclideanSpace ℝ (Fin 3) → ℝ) z + g z)
            = g from by funext z; simp,
        show (fun z : EuclideanSpace ℝ (Fin 3) => (0 : EuclideanSpace ℝ (Fin 3) → ℝ) z - g z)
            = (fun z => - g z) from by funext z; simp,
        fsT_fun_neg]
      ring
  | insert a σ ha ih =>
      have ha' : ContDiff ℝ (⊤ : ℕ∞) (u a) := hu a (Finset.mem_insert_self a σ)
      have hs' : ∀ i ∈ σ, ContDiff ℝ (⊤ : ℕ∞) (u i) :=
        fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ i ∈ σ, u i z) := contDiff_finsetSum σ hs'
      have hsplit : (fun z : EuclideanSpace ℝ (Fin 3) => ∑ i ∈ insert a σ, u i z)
          = (fun z => u a z + ∑ i ∈ σ, u i z) := by
        funext z
        simp only [Finset.sum_insert ha]
      rw [hsplit, Finset.sum_insert ha]
      rw [KinOffdiag.fsTbil_add_left (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
        (f := u a) (g := fun z => ∑ i ∈ σ, u i z) (h := g) hℓ ha' hsum hg]
      rw [ih hs']

/-- Additivity of `fsTbil` in a finite sum in its second slot. -/
lemma fsTbil_sum_right {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {ι : Type*} (σ : Finset ι)
    {v : ι → EuclideanSpace ℝ (Fin 3) → ℝ} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : ∀ i ∈ σ, ContDiff ℝ (⊤ : ℕ∞) (v i)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    fsTbil ℓ d s εT b 0 f (fun z => ∑ i ∈ σ, v i z)
      = ∑ i ∈ σ, fsTbil ℓ d s εT b 0 f (v i) := by
  classical
  rw [fsTbil_symm f (fun z => ∑ i ∈ σ, v i z)]
  rw [fsTbil_sum_left (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ σ hv hf]
  exact Finset.sum_congr rfl (fun i _ => fsTbil_symm (v i) f)

/-! ## 5. The pointwise expansion over the sectors -/

/-- **The polarisation of the slot form expands over the joint projections.**  For every slot
`a` and every configuration `x`, the polarisation of the slot-`a` kinetic form at the two
sectors `sᵢΦ = Σ_{|S|=i}E_SΦ`, `sₖΦ = Σ_{|T|=k}E_TΦ` is the double sum of the polarisations at
the joint projections `E_SΦ`, `E_TΦ`. -/
lemma fsTbil_secProj_expand {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i k : ℕ) (a : Fin n)
    (x : Submission.BoseGases.X n) :
    fsTbil ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ) x) (fibre n a (secProj ℓ k Φ) x)
      = ∑ S ∈ (Finset.range n).powersetCard i, ∑ T ∈ (Finset.range n).powersetCard k,
          fsTbil ℓ d s εT b 0 (fibre n a (jointProj ℓ S Φ) x) (fibre n a (jointProj ℓ T Φ) x) := by
  classical
  rw [fibre_secProj a ℓ i Φ x, fibre_secProj a ℓ k Φ x]
  -- smoothness of the individual fibres
  have hu : ∀ S ∈ (Finset.range n).powersetCard i,
      ContDiff ℝ (⊤ : ℕ∞) (fibre n a (jointProj ℓ S Φ) x) :=
    fun S _ => Work.BoseFixB2.Polar.contDiff_fibre (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ) a x
  have hv : ∀ T ∈ (Finset.range n).powersetCard k,
      ContDiff ℝ (⊤ : ℕ∞) (fibre n a (jointProj ℓ T Φ) x) :=
    fun T _ => Work.BoseFixB2.Polar.contDiff_fibre (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ) a x
  have hL : (∑ S ∈ (Finset.range n).powersetCard i, fibre n a (jointProj ℓ S Φ) x)
      = (fun z => ∑ S ∈ (Finset.range n).powersetCard i,
          fibre n a (jointProj ℓ S Φ) x z) := by
    funext z; simp only [Finset.sum_apply]
  have hR : (∑ T ∈ (Finset.range n).powersetCard k, fibre n a (jointProj ℓ T Φ) x)
      = (fun z => ∑ T ∈ (Finset.range n).powersetCard k,
          fibre n a (jointProj ℓ T Φ) x z) := by
    funext z; simp only [Finset.sum_apply]
  rw [hL, hR]
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∑ T ∈ (Finset.range n).powersetCard k, fibre n a (jointProj ℓ T Φ) x z) :=
    contDiff_finsetSum ((Finset.range n).powersetCard k) hv
  rw [fsTbil_sum_left (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ
    ((Finset.range n).powersetCard i) hu hg]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  exact fsTbil_sum_right (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ
    ((Finset.range n).powersetCard k) hv (hu S hS)

/-- `secProj ℓ k Φ` is smooth (no symmetry hypothesis). -/
lemma secProj_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (k : ℕ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (secProj ℓ k Φ) := by
  have hfun : (secProj ℓ k Φ)
      = (fun x => ∑ S ∈ (Finset.range n).powersetCard k, jointProj ℓ S Φ x) := by
    rw [secProj]
    funext x
    simp only [Finset.sum_apply]
  rw [hfun]
  exact contDiff_finsetSum (σ := (Finset.range n).powersetCard k)
    (u := fun S => jointProj ℓ S Φ) (fun S _ => Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ)

/-- **The polarisation of the slot form expands over the joint projections** — the form in
which the expansion is consumed: the polarisation at the two sectors is the double sum of the
polarisations at the joint projections. -/
lemma fsT_secProj_expand {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i k : ℕ) (a : Fin n)
    (x : Submission.BoseGases.X n) :
    (fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
      - fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x)) / 4
      = ∑ S ∈ (Finset.range n).powersetCard i, ∑ T ∈ (Finset.range n).powersetCard k,
          (fsT ℓ d s εT b 0 (fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
            - fsT ℓ d s εT b 0 (fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x)) / 4 := by
  have h1 := fsTbil_secProj_expand (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ hΦ i k a x
  have e1 : fsTbil ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ) x) (fibre n a (secProj ℓ k Φ) x)
      = (fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
        - fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x)) / 4 := by
    unfold Work.BoseFixB2.fsTbil
    rfl
  rw [e1] at h1
  rw [h1]
  refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
  unfold Work.BoseFixB2.fsTbil
  rfl

/-! ## 6. The vanishing at a slot in `S ∩ T` (delegated)

The per-slot vanishing at a slot `a ∈ S ∩ T` with `S ≠ T` is the assembly of the off-diagonal
vanishing of the four summands of `fsT`; it is proved in
`Submission/Work/BoseFixB2/DvApriori/KinOffdiag/slotTerm_zero_of_mem.lean` (together with the
integrability of the four summands in `KinOffdiag/pieces_integrableOn_fibre`). -/

theorem slotTerm_zero_of_mem {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (a : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (haS : (a : ℕ) ∈ S) (haT : (a : ℕ) ∈ T) (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) / 4) = 0 :=
  KinOffdiag.slotTerm_zero_of_mem hℓ a hΦ hS hT haS haT hST

/-! ## 7. Integrability of the polarised slot integrand -/

/-- Integrability of the `1/4`-weighted polarised slot integrand of two smooth states. -/
lemma integrableOn_slotTerm {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (a : Fin n)
    {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (Φ + Ψ) x)
          - Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (Φ - Ψ) x))) / 4)
      (Submission.BoseGases.abox n ℓ) := by
  have h1 := Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) (b := b) hℓ a (hΦ.add hΨ)
  have h2 := Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) (b := b) hℓ a (hΦ.sub hΨ)
  have h3 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (fun x => Φ x + Ψ x) x)
          - Work.BoseKinLoc.fsT ℓ d s εT b 0
              (Work.BoseKinLoc.fibre n a (fun x => Φ x - Ψ x) x))) / 4)
      (Submission.BoseGases.abox n ℓ) := by
    have h := (h1.sub h2).const_mul ((1 : ℝ) / 4)
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.sub_apply, div_eq_inv_mul]
    ring
  have e1 : (fun y : Submission.BoseGases.X n => Φ y + Ψ y) = (Φ + Ψ) := by
    funext y; rfl
  have e2 : (fun y : Submission.BoseGases.X n => Φ y - Ψ y) = (Φ - Ψ) := by
    funext y; rfl
  have e1' : (fun x : Submission.BoseGases.X n => Φ x + Ψ x)
      = (fun y : Submission.BoseGases.X n => Φ y + Ψ y) := rfl
  have e2' : (fun x : Submission.BoseGases.X n => Φ x - Ψ x)
      = (fun y : Submission.BoseGases.X n => Φ y - Ψ y) := rfl
  rw [e1', e2'] at h3
  rwa [e1, e2] at h3

/-- The pointwise expansion of the sector polarisation, without the `1/4` factor. -/
lemma fsT_secProj_expand' {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i k : ℕ) (a : Fin n)
    (x : Submission.BoseGases.X n) :
    (fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
      - fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x))
      = ∑ S ∈ (Finset.range n).powersetCard i, ∑ T ∈ (Finset.range n).powersetCard k,
          (fsT ℓ d s εT b 0 (fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
            - fsT ℓ d s εT b 0 (fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x)) := by
  have h1 := fsTbil_secProj_expand (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ hΦ i k a x
  have e1 : (fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
        - fsT ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x))
      = 4 * fsTbil ℓ d s εT b 0 (fibre n a (secProj ℓ i Φ) x) (fibre n a (secProj ℓ k Φ) x) := by
    rw [show (fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
        = (fun z => (fibre n a (secProj ℓ i Φ) x) z + (fibre n a (secProj ℓ k Φ) x) z)
        from rfl,
      show (fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x)
        = (fun z => (fibre n a (secProj ℓ i Φ) x) z - (fibre n a (secProj ℓ k Φ) x) z)
        from rfl]
    unfold Work.BoseFixB2.fsTbil
    ring
  rw [e1, h1, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [show (fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
      = (fun z => (fibre n a (jointProj ℓ S Φ) x) z + (fibre n a (jointProj ℓ T Φ) x) z)
      from rfl,
    show (fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x)
      = (fun z => (fibre n a (jointProj ℓ S Φ) x) z - (fibre n a (jointProj ℓ T Φ) x) z)
      from rfl]
  unfold Work.BoseFixB2.fsTbil
  ring

/-! ## 8. The main theorem -/

theorem kinFormB_secProj_offdiag {ℓ : ℝ} (hℓ : 0 < ℓ) {d s εT b : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {i k : ℕ} (hik : i ≠ k) :
    (Work.BoseKinLoc.kinFormB n ℓ d s εT b
        (Work.BoseFixB2.secProj ℓ i Φ + Work.BoseFixB2.secProj ℓ k Φ)
      - Work.BoseKinLoc.kinFormB n ℓ d s εT b
        (Work.BoseFixB2.secProj ℓ i Φ - Work.BoseFixB2.secProj ℓ k Φ)) / 4 = 0 := by
  classical
  have hΞ : ContDiff ℝ (⊤ : ℕ∞) (secProj ℓ i Φ) := secProj_contDiff hℓ i hΦ
  have hΗ : ContDiff ℝ (⊤ : ℕ∞) (secProj ℓ k Φ) := secProj_contDiff hℓ k hΦ
  have hΞΗ : ContDiff ℝ (⊤ : ℕ∞) (secProj ℓ i Φ + secProj ℓ k Φ) := hΞ.add hΗ
  have hΞm : ContDiff ℝ (⊤ : ℕ∞) (secProj ℓ i Φ - secProj ℓ k Φ) := hΞ.sub hΗ
  -- integrability of the two slot integrands of the two sectors
  have hIntP : ∀ a : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (x a) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x))
      (Submission.BoseGases.abox n ℓ) :=
    fun a => Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
      (εT := εT) (b := b) hℓ a hΞΗ
  have hIntM : ∀ a : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (x a) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x))
      (Submission.BoseGases.abox n ℓ) :=
    fun a => Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
      (εT := εT) (b := b) hℓ a hΞm
  -- (1) expand `kinFormB` and put the difference inside the sum
  have hJ : ∀ a : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x))
        - (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x))
      = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
          (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
           - Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x)) := by
    intro a
    rw [← MeasureTheory.integral_sub (hIntP a) (hIntM a)]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => ?_)
    ring
  have step1 : (Work.BoseKinLoc.kinFormB n ℓ d s εT b
          (secProj ℓ i Φ + secProj ℓ k Φ)
        - Work.BoseKinLoc.kinFormB n ℓ d s εT b
          (secProj ℓ i Φ - secProj ℓ k Φ))
      = ℓ ^ (-3 : ℤ) * ∑ a : Fin n,
          ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
            (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
             - Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x)) := by
    unfold Work.BoseKinLoc.kinFormB
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hJ a)]
  -- (2) expand each slot over the joint projections
  have step2 : ∀ a : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
          (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
           - Work.BoseKinLoc.fsT ℓ d s εT b 0
              (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x)))
      = ∑ S ∈ (Finset.range n).powersetCard i, ∑ T ∈ (Finset.range n).powersetCard k,
          ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
            (Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
             - Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x)) := by
    intro a
    -- the pointwise identity (without the `1/4`)
    have hpt : ∀ x : Submission.BoseGases.X n,
        Work.BoseKinLoc.indU ℓ 0 (x a) *
          (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ + secProj ℓ k Φ) x)
           - Work.BoseKinLoc.fsT ℓ d s εT b 0
              (Work.BoseKinLoc.fibre n a (secProj ℓ i Φ - secProj ℓ k Φ) x))
        = ∑ S ∈ (Finset.range n).powersetCard i, ∑ T ∈ (Finset.range n).powersetCard k,
            Work.BoseKinLoc.indU ℓ 0 (x a) *
              (Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
               - Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x)) := by
      intro x
      rw [fsT_secProj_expand' (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ hΦ i k a x,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      rw [Finset.mul_sum]
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => hpt x)]
    have hterm : ∀ S T : Finset ℕ, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x a) *
          (Work.BoseKinLoc.fsT ℓ d s εT b 0
              (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
           - Work.BoseKinLoc.fsT ℓ d s εT b 0
              (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x)))
        (Submission.BoseGases.abox n ℓ) :=
      fun S T =>
        ((Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
            (εT := εT) (b := b) hℓ a
            ((Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).add
              (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ))).sub
          (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
            (εT := εT) (b := b) hℓ a
            ((Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).sub
              (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ)))).congr
          (Filter.Eventually.of_forall (fun x => by
            rw [show (fun x : Submission.BoseGases.X n => jointProj ℓ S Φ x + jointProj ℓ T Φ x)
                  = (jointProj ℓ S Φ + jointProj ℓ T Φ) from rfl,
              show (fun x : Submission.BoseGases.X n => jointProj ℓ S Φ x - jointProj ℓ T Φ x)
                  = (jointProj ℓ S Φ - jointProj ℓ T Φ) from rfl]
            simp only [Pi.sub_apply]
            ring))
    have houter := MeasureTheory.integral_finsetSum ((Finset.range n).powersetCard i)
      (f := fun S : Finset ℕ => fun x : Submission.BoseGases.X n =>
        ∑ T ∈ (Finset.range n).powersetCard k,
          Work.BoseKinLoc.indU ℓ 0 (x a) *
            (Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
             - Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x)))
      (fun S _ => MeasureTheory.integrable_finsetSum ((Finset.range n).powersetCard k)
        (fun T _ => hterm S T))
    rw [houter]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    exact MeasureTheory.integral_finsetSum ((Finset.range n).powersetCard k)
      (fun T _ => hterm S T)
  rw [step1]
  rw [Finset.sum_congr rfl (fun a _ => step2 a)]
  -- (3) each term vanishes
  have step3 : ∀ (a : Fin n) (S T : Finset ℕ), S ∈ (Finset.range n).powersetCard i →
      T ∈ (Finset.range n).powersetCard k →
      (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
         - Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x))) = 0 := by
    intro a S T hS hT
    have hSr : S ⊆ Finset.range n := (Finset.mem_powersetCard.mp hS).1
    have hTr : T ⊆ Finset.range n := (Finset.mem_powersetCard.mp hT).1
    have hcardS : S.card = i := (Finset.mem_powersetCard.mp hS).2
    have hcardT : T.card = k := (Finset.mem_powersetCard.mp hT).2
    have hST : S ≠ T := by
      intro h
      rw [← h] at hcardT
      exact hik (hcardS.symm.trans hcardT)
    by_cases haS : (a : ℕ) ∈ S
    · by_cases haT : (a : ℕ) ∈ T
      · have h := slotTerm_zero_of_mem (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ a hΦ
          hSr hTr haS haT hST
        have h2 : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
            (Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
             - Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x))) = 0 := by
          rw [MeasureTheory.integral_div] at h
          have h3 := h
          rw [div_eq_mul_inv] at h3
          exact (mul_eq_zero.mp h3).resolve_right (by norm_num)
        exact h2
      · exact KinOffdiag.kinFormB_offdiag_of_notMem (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ a hΦ
          hSr hTr (Or.inr haT)
    · exact KinOffdiag.kinFormB_offdiag_of_notMem (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ a hΦ
        hSr hTr (Or.inl haS)
  have hzero : ∀ a : Fin n,
      (∑ S ∈ (Finset.range n).powersetCard i, ∑ T ∈ (Finset.range n).powersetCard k,
          ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
            (Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ + jointProj ℓ T Φ) x)
             - Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n a (jointProj ℓ S Φ - jointProj ℓ T Φ) x))) = 0 := by
    intro a
    refine Finset.sum_eq_zero (fun S hS => ?_)
    refine Finset.sum_eq_zero (fun T hT => ?_)
    exact step3 a S T hS hT
  rw [Finset.sum_congr rfl (fun a _ => hzero a)]
  simp

end Work.BoseFixB2.DvApriori
