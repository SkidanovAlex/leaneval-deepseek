/-
  `Work.WilG4c.SectLocusMem` — the fixed-point locus of a composition of two `Ω`-definable
  maps is `Ω`-definable, with polynomial format/degree bounds.

  Given `θ : ℝ^q → ℝ^p` whose `p` coordinate graphs are `Ω Aθ (bθ) (q+1)` and
  `μ : ℝ^p → ℝ^q` whose `q` coordinate graphs are `Ω Aμ (bμ) (p+1)`, the set
  `{l : ℝ^p | θ (μ l) = l}` is `Ω (Aθ + Aμ + AP) (p·(bθ + q·bμ) + DP) p`.

  The proof works in `ℝ^{p+q}`, laid out as `(l, ν)` with `l` the first `p` coordinates and
  `ν` the last `q`:

  * `sdmThetaBlk` is the set `{z | ∀ i, z (castAdd q i) = θ (fun j => z (natAdd p j)) i}`,
    the intersection of the `p` coordinate pullbacks `z ∘ sigTheta_i` of the graphs of the
    coordinates of `θ` (`ZzSubstOmega`: format `+2*((p+q)+(q+1))+1`, degree `+2` each);
  * `sdmMuBlk` is the set `{z | ∀ j, z (natAdd p j) = μ (fun i => z (castAdd q i)) j}`, the
    intersection of the `q` coordinate pullbacks `z ∘ sigMu_j` of the graphs of the
    coordinates of `μ`;
  * the fixed-point locus is the projection of `sdmThetaBlk ∩ sdmMuBlk` away from the last
    `q` coordinates (`Work.WilG0.projLastIter_mem`), which costs `q + p` in the format and
    nothing in the degree;
  * the degree comparison `p·(bθ+2) + q·(bμ+2) ≤ p·(bθ + q·bμ) + DP` is where the shape
    `C p * (bθ + C q * bμ)` comes from: since `p ≥ 1`, `q·bμ ≤ p·(q·bμ)`.  The degenerate
    case `p = 0` is handled separately: the locus is then all of `ℝ^0 = Fin 0 → ℝ`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.ZzSubstOmega

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## 1. The index maps of the two coordinate conditions -/

/-- In `ℝ^{p+q}` (leading block `l : Fin p`, trailing block `ν : Fin q`), the substitution
selecting `(l, ν_j)`: the `p` arguments in front, the `j`-th value at the end. -/
def sdmSigMu (p q : ℕ) (j : Fin q) : Fin (p + 1) → Fin (p + q) :=
  Fin.snoc (fun i : Fin p => Fin.castAdd q i) (Fin.natAdd p j)

@[simp] theorem sdmSigMu_last (p q : ℕ) (j : Fin q) :
    sdmSigMu p q j (Fin.last p) = Fin.natAdd p j := by
  simp [sdmSigMu]

@[simp] theorem sdmSigMu_castSucc (p q : ℕ) (j : Fin q) (i : Fin p) :
    sdmSigMu p q j (Fin.castSucc i) = Fin.castAdd q i := by
  simp [sdmSigMu]

/-- In `ℝ^{p+q}`, the substitution selecting `(ν, l_i)`: the `q` arguments in front, the
`i`-th value at the end. -/
def sdmSigTheta (p q : ℕ) (i : Fin p) : Fin (q + 1) → Fin (p + q) :=
  Fin.snoc (fun j : Fin q => Fin.natAdd p j) (Fin.castAdd q i)

@[simp] theorem sdmSigTheta_last (p q : ℕ) (i : Fin p) :
    sdmSigTheta p q i (Fin.last q) = Fin.castAdd q i := by
  simp [sdmSigTheta]

@[simp] theorem sdmSigTheta_castSucc (p q : ℕ) (i : Fin p) (j : Fin q) :
    sdmSigTheta p q i (Fin.castSucc j) = Fin.natAdd p j := by
  simp [sdmSigTheta]

/-! ## 2. The two blocks -/

/-- The θ-block in `ℝ^{p+q}`: `l = θ ν` (first `p` coordinates the vector `l`, last `q` the
argument `ν`). -/
def sdmThetaBlk (p q : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)) : Set (Fin (p + q) → ℝ) :=
  {z | ∀ i : Fin p, z (Fin.castAdd q i) = θ (fun j : Fin q => z (Fin.natAdd p j)) i}

/-- The μ-block in `ℝ^{p+q}`: `ν = μ l`. -/
def sdmMuBlk (p q : ℕ) (μ : (Fin p → ℝ) → (Fin q → ℝ)) : Set (Fin (p + q) → ℝ) :=
  {z | ∀ j : Fin q, z (Fin.natAdd p j) = μ (fun i : Fin p => z (Fin.castAdd q i)) j}

/-! ## 3. The coordinate pullbacks -/

theorem sdmMem_sigTheta_graph (p q : ℕ) (i : Fin p) (θ : (Fin q → ℝ) → (Fin p → ℝ))
    (z : Fin (p + q) → ℝ) :
    z ∘ sdmSigTheta p q i ∈ WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν i) ↔
      z (Fin.castAdd q i) = θ (fun j : Fin q => z (Fin.natAdd p j)) i := by
  have h1 : Fin.init (z ∘ sdmSigTheta p q i) = fun j : Fin q => z (Fin.natAdd p j) := by
    funext j
    show (z ∘ sdmSigTheta p q i) (Fin.castSucc j) = z (Fin.natAdd p j)
    rw [Function.comp_apply, sdmSigTheta_castSucc]
  have h2 : (z ∘ sdmSigTheta p q i) (Fin.last q) = z (Fin.castAdd q i) := by
    rw [Function.comp_apply, sdmSigTheta_last]
  rw [WilkiesDesign.graphOf, Set.mem_ofPred_eq, h1, h2]

theorem sdmMem_sigMu_graph (p q : ℕ) (j : Fin q) (μ : (Fin p → ℝ) → (Fin q → ℝ))
    (z : Fin (p + q) → ℝ) :
    z ∘ sdmSigMu p q j ∈ WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ↔
      z (Fin.natAdd p j) = μ (fun i : Fin p => z (Fin.castAdd q i)) j := by
  have h1 : Fin.init (z ∘ sdmSigMu p q j) = fun i : Fin p => z (Fin.castAdd q i) := by
    funext i
    show (z ∘ sdmSigMu p q j) (Fin.castSucc i) = z (Fin.castAdd q i)
    rw [Function.comp_apply, sdmSigMu_castSucc]
  have h2 : (z ∘ sdmSigMu p q j) (Fin.last p) = z (Fin.natAdd p j) := by
    rw [Function.comp_apply, sdmSigMu_last]
  rw [WilkiesDesign.graphOf, Set.mem_ofPred_eq, h1, h2]

/-- The θ-block is the intersection of its `p` coordinate conditions. -/
theorem sdmThetaBlk_eq_iInter (p q : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)) :
    sdmThetaBlk p q θ = ⋂ i : Fin p, {z : Fin (p + q) → ℝ |
      z ∘ sdmSigTheta p q i ∈ WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν i)} := by
  ext z
  simp only [sdmThetaBlk, Set.mem_ofPred_eq, Set.mem_iInter]
  exact ⟨fun h i => (sdmMem_sigTheta_graph p q i θ z).mpr (h i),
    fun h i => (sdmMem_sigTheta_graph p q i θ z).mp (h i)⟩

/-- The μ-block is the intersection of its `q` coordinate conditions. -/
theorem sdmMuBlk_eq_iInter (p q : ℕ) (μ : (Fin p → ℝ) → (Fin q → ℝ)) :
    sdmMuBlk p q μ = ⋂ j : Fin q, {z : Fin (p + q) → ℝ |
      z ∘ sdmSigMu p q j ∈ WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j)} := by
  ext z
  simp only [sdmMuBlk, Set.mem_ofPred_eq, Set.mem_iInter]
  exact ⟨fun h j => (sdmMem_sigMu_graph p q j μ z).mpr (h j),
    fun h j => (sdmMem_sigMu_graph p q j μ z).mp (h j)⟩

/-! ## 4. `Ω`-membership of the two blocks -/

theorem sdmThetaBlk_mem (S : WilkiesDesign.SOMin) (p q : ℕ) :
    ∃ C : ℕ, ∀ (Aθ : ℕ) (bθ : MvPolynomial (Fin 2) ℕ) (D r : ℕ)
      (θ : (Fin q → ℝ) → (Fin p → ℝ)),
      (∀ i : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν i) ∈
        S.Ω Aθ (MvPolynomial.eval ![D, r] bθ) (q + 1)) →
      sdmThetaBlk p q θ ∈
        S.Ω (Aθ + C)
          (MvPolynomial.eval ![D, r] (MvPolynomial.C p * bθ + MvPolynomial.C C)) (p + q) := by
  refine ⟨2 * ((p + q) + (q + 1)) + 2, ?_⟩
  intro Aθ bθ D r θ hθ
  rw [sdmThetaBlk_eq_iInter]
  have hsub : ∀ i : Fin p, {z : Fin (p + q) → ℝ |
      z ∘ sdmSigTheta p q i ∈ WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν i)} ∈
      S.Ω (Aθ + 2 * ((p + q) + (q + 1)) + 1)
        (MvPolynomial.eval ![D, r] bθ + 2) (p + q) :=
    fun i => ZzSubstOmega S (sdmSigTheta p q i) (hθ i)
  have hint := S.inter (D := fun _ : Fin p => MvPolynomial.eval ![D, r] bθ + 2)
    (A := fun i : Fin p => {z : Fin (p + q) → ℝ |
      z ∘ sdmSigTheta p q i ∈ WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν i)}) hsub
  have hsum : (∑ _ : Fin p, (MvPolynomial.eval ![D, r] bθ + 2)) =
      p * (MvPolynomial.eval ![D, r] bθ + 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  rw [hsum] at hint
  have hdeg : p * (MvPolynomial.eval ![D, r] bθ + 2) ≤
      MvPolynomial.eval ![D, r]
        (MvPolynomial.C p * bθ + MvPolynomial.C (2 * ((p + q) + (q + 1)) + 2)) := by
    rw [show MvPolynomial.eval ![D, r]
        (MvPolynomial.C p * bθ + MvPolynomial.C (2 * ((p + q) + (q + 1)) + 2))
        = p * MvPolynomial.eval ![D, r] bθ + (2 * ((p + q) + (q + 1)) + 2) from by simp]
    rw [Nat.mul_add]
    omega
  have hF : (Aθ + 2 * ((p + q) + (q + 1)) + 1) + 1 ≤
      Aθ + (2 * ((p + q) + (q + 1)) + 2) := by omega
  exact Work.WilkG4c.Omega_mono_le S hF hdeg hint

theorem sdmMuBlk_mem (S : WilkiesDesign.SOMin) (p q : ℕ) :
    ∃ C : ℕ, ∀ (Aμ : ℕ) (bμ : MvPolynomial (Fin 2) ℕ) (D r : ℕ)
      (μ : (Fin p → ℝ) → (Fin q → ℝ)),
      (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
        S.Ω Aμ (MvPolynomial.eval ![D, r] bμ) (p + 1)) →
      sdmMuBlk p q μ ∈
        S.Ω (Aμ + C)
          (MvPolynomial.eval ![D, r] (MvPolynomial.C q * bμ + MvPolynomial.C C)) (p + q) := by
  refine ⟨2 * ((p + q) + (p + 1)) + 2, ?_⟩
  intro Aμ bμ D r μ hμ
  rw [sdmMuBlk_eq_iInter]
  have hsub : ∀ j : Fin q, {z : Fin (p + q) → ℝ |
      z ∘ sdmSigMu p q j ∈ WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j)} ∈
      S.Ω (Aμ + 2 * ((p + q) + (p + 1)) + 1)
        (MvPolynomial.eval ![D, r] bμ + 2) (p + q) :=
    fun j => ZzSubstOmega S (sdmSigMu p q j) (hμ j)
  have hint := S.inter (D := fun _ : Fin q => MvPolynomial.eval ![D, r] bμ + 2)
    (A := fun j : Fin q => {z : Fin (p + q) → ℝ |
      z ∘ sdmSigMu p q j ∈ WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j)}) hsub
  have hsum : (∑ _ : Fin q, (MvPolynomial.eval ![D, r] bμ + 2)) =
      q * (MvPolynomial.eval ![D, r] bμ + 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  rw [hsum] at hint
  have hdeg : q * (MvPolynomial.eval ![D, r] bμ + 2) ≤
      MvPolynomial.eval ![D, r]
        (MvPolynomial.C q * bμ + MvPolynomial.C (2 * ((p + q) + (p + 1)) + 2)) := by
    rw [show MvPolynomial.eval ![D, r]
        (MvPolynomial.C q * bμ + MvPolynomial.C (2 * ((p + q) + (p + 1)) + 2))
        = q * MvPolynomial.eval ![D, r] bμ + (2 * ((p + q) + (p + 1)) + 2) from by simp]
    rw [Nat.mul_add]
    omega
  have hF : (Aμ + 2 * ((p + q) + (p + 1)) + 1) + 1 ≤
      Aμ + (2 * ((p + q) + (p + 1)) + 2) := by omega
  exact Work.WilkG4c.Omega_mono_le S hF hdeg hint

/-! ## 5. The projection of the intersection is the fixed-point locus -/

theorem sdmMem_thetaBlk {p q : ℕ} (θ : (Fin q → ℝ) → (Fin p → ℝ)) (z : Fin (p + q) → ℝ) :
    z ∈ sdmThetaBlk p q θ ↔
      (fun i : Fin p => z (Fin.castAdd q i)) = θ (fun j : Fin q => z (Fin.natAdd p j)) := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

theorem sdmMem_muBlk {p q : ℕ} (μ : (Fin p → ℝ) → (Fin q → ℝ)) (z : Fin (p + q) → ℝ) :
    z ∈ sdmMuBlk p q μ ↔
      (fun j : Fin q => z (Fin.natAdd p j)) = μ (fun i : Fin p => z (Fin.castAdd q i)) := by
  constructor
  · intro h
    funext j
    exact h j
  · intro h j
    exact congrFun h j

theorem sdmProjLastIter_inter (p q : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ))
    (μ : (Fin p → ℝ) → (Fin q → ℝ)) :
    Work.WilG0.projLastIter p q (sdmThetaBlk p q θ ∩ sdmMuBlk p q μ) =
      {l : Fin p → ℝ | θ (μ l) = l} := by
  rw [Work.WilG0.projLastIter_eq]
  ext x
  constructor
  · rintro ⟨w, hw⟩
    rw [Set.mem_inter_iff] at hw
    obtain ⟨h1, h2⟩ := hw
    have hc : (fun i : Fin p => Work.WilG0.snocIt p q x w (Fin.castAdd q i)) = x :=
      funext fun i => Work.WilG0.snocIt_castAdd p q x w i
    have hn : (fun j : Fin q => Work.WilG0.snocIt p q x w (Fin.natAdd p j)) = w :=
      funext fun j => Work.WilG0.snocIt_natAdd p q x w j
    have hth : x = θ w := by
      have h1' := (sdmMem_thetaBlk θ (Work.WilG0.snocIt p q x w)).mp h1
      rw [hc, hn] at h1'
      exact h1'
    have hmu : w = μ x := by
      have h2' := (sdmMem_muBlk μ (Work.WilG0.snocIt p q x w)).mp h2
      rw [hn, hc] at h2'
      exact h2'
    show θ (μ x) = x
    rw [← hmu, ← hth]
  · intro hx
    refine ⟨μ x, ?_⟩
    rw [Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · rw [sdmMem_thetaBlk]
      have hc : (fun i : Fin p => Work.WilG0.snocIt p q x (μ x) (Fin.castAdd q i)) = x :=
        funext fun i => Work.WilG0.snocIt_castAdd p q x (μ x) i
      have hn : (fun j : Fin q => Work.WilG0.snocIt p q x (μ x) (Fin.natAdd p j)) = μ x :=
        funext fun j => Work.WilG0.snocIt_natAdd p q x (μ x) j
      rw [hc, hn]
      exact hx.symm
    · rw [sdmMem_muBlk]
      have hc : (fun i : Fin p => Work.WilG0.snocIt p q x (μ x) (Fin.castAdd q i)) = x :=
        funext fun i => Work.WilG0.snocIt_castAdd p q x (μ x) i
      have hn : (fun j : Fin q => Work.WilG0.snocIt p q x (μ x) (Fin.natAdd p j)) = μ x :=
        funext fun j => Work.WilG0.snocIt_natAdd p q x (μ x) j
      rw [hn, hc]

/-! ## 6. Assembly -/

theorem SectLocusMem (S : WilkiesDesign.SOMin) (p q : ℕ) :
    ∃ (AP : ℕ) (DP : ℕ),
      ∀ (Aθ : ℕ) (bθ : MvPolynomial (Fin 2) ℕ) (Aμ : ℕ) (bμ : MvPolynomial (Fin 2) ℕ)
        (D r : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)) (μ : (Fin p → ℝ) → (Fin q → ℝ)),
        (∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
          S.Ω Aθ (MvPolynomial.eval ![D, r] bθ) (q + 1)) →
        (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
          S.Ω Aμ (MvPolynomial.eval ![D, r] bμ) (p + 1)) →
        {l : Fin p → ℝ | θ (μ l) = l} ∈
          S.Ω (Aθ + Aμ + AP)
            (MvPolynomial.eval ![D, r]
              (MvPolynomial.C p * (bθ + MvPolynomial.C q * bμ) + MvPolynomial.C DP)) p := by
  by_cases hp : p = 0
  · -- degenerate case: for `p = 0` the locus is all of `ℝ^0`
    subst hp
    refine ⟨1, 0, ?_⟩
    intro Aθ bθ Aμ bμ D r θ μ hθ hμ
    have hset : {l : Fin 0 → ℝ | θ (μ l) = l} = (Set.univ : Set (Fin 0 → ℝ)) := by
      ext l
      constructor
      · intro _
        trivial
      · intro _
        funext i
        exact i.elim0
    rw [hset]
    have hdeg : MvPolynomial.eval ![D, r]
        (MvPolynomial.C 0 * (bθ + MvPolynomial.C q * bμ) + MvPolynomial.C 0) = 0 := by
      simp
    rw [hdeg]
    exact Work.WilkG4c.Omega_mono_le S (by omega) (by omega)
      (Work.WilkG4c.Omega_univ S 0 0)
  · have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
    obtain ⟨Cθ, hθblk⟩ := sdmThetaBlk_mem S p q
    obtain ⟨Cμ, hμblk⟩ := sdmMuBlk_mem S p q
    refine ⟨Cθ + Cμ + (1 + q + p), Cθ + Cμ, ?_⟩
    intro Aθ bθ Aμ bμ D r θ μ hθ hμ
    have h1 := hθblk Aθ bθ D r θ hθ
    have h2 := hμblk Aμ bμ D r μ hμ
    have h1' : sdmThetaBlk p q θ ∈ S.Ω ((Aθ + Cθ) + (Aμ + Cμ))
        (MvPolynomial.eval ![D, r] (MvPolynomial.C p * bθ + MvPolynomial.C Cθ)) (p + q) :=
      Work.WilkG4c.Omega_mono_le S (by omega) le_rfl h1
    have h2' : sdmMuBlk p q μ ∈ S.Ω ((Aθ + Cθ) + (Aμ + Cμ))
        (MvPolynomial.eval ![D, r] (MvPolynomial.C q * bμ + MvPolynomial.C Cμ)) (p + q) :=
      Work.WilkG4c.Omega_mono_le S (by omega) le_rfl h2
    have hint := Work.WilG0.Omega_inter2 h1' h2'
    have hproj := Work.WilG0.projLastIter_mem S p q ((Aθ + Cθ) + (Aμ + Cμ) + 1)
      (MvPolynomial.eval ![D, r] (MvPolynomial.C p * bθ + MvPolynomial.C Cθ)
        + MvPolynomial.eval ![D, r] (MvPolynomial.C q * bμ + MvPolynomial.C Cμ))
      _ hint
    rw [sdmProjLastIter_inter] at hproj
    refine Work.WilkG4c.Omega_mono_le S ?_ ?_ hproj
    · omega
    · have hev1 : MvPolynomial.eval ![D, r] (MvPolynomial.C p * bθ + MvPolynomial.C Cθ)
          = p * MvPolynomial.eval ![D, r] bθ + Cθ := by
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      have hev2 : MvPolynomial.eval ![D, r] (MvPolynomial.C q * bμ + MvPolynomial.C Cμ)
          = q * MvPolynomial.eval ![D, r] bμ + Cμ := by
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      have htarget : MvPolynomial.eval ![D, r]
          (MvPolynomial.C p * (bθ + MvPolynomial.C q * bμ) + MvPolynomial.C (Cθ + Cμ))
          = p * (MvPolynomial.eval ![D, r] bθ + q * MvPolynomial.eval ![D, r] bμ)
            + (Cθ + Cμ) := by
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      rw [hev1, hev2, htarget]
      have hmul : q * MvPolynomial.eval ![D, r] bμ ≤
          p * (q * MvPolynomial.eval ![D, r] bμ) := by
        have h := Nat.mul_le_mul_left (q * MvPolynomial.eval ![D, r] bμ) hp1
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      have hexp : p * (MvPolynomial.eval ![D, r] bθ + q * MvPolynomial.eval ![D, r] bμ)
          = p * MvPolynomial.eval ![D, r] bθ
            + p * (q * MvPolynomial.eval ![D, r] bμ) := Nat.mul_add _ _ _
      rw [hexp]
      omega

end Work.WilG4c
