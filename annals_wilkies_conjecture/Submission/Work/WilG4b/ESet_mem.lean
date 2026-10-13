/-
  Area G4b: `ESet_mem`.

  The choice set `ESet f c d M` (the `C¹` points `z` of `ℝ^{n+1}` with `z 0 ∈ (c,d)`,
  `Fin.tail z` in the open cube, and `|∂₀ f(z)| > M (1 + n u)` for a common bound `u` of the
  `y`-partials) is an `Ω`-set, with format `F + K` and degree a polynomial in `D` whenever
  `graphOf f ∈ S.Ω F D (n+2)`.

  The proof is a calculation in the frozen `Ω`-calculus:

  * `SharpDeriv` at order one exhibits the derivative graphs `derivGraph f i`, hence (by
    `uniform_pullback_mem`) the sets `ECond f i` of the joint space `ℝ^{(n+1)+(n+1)+1}` and
    their intersection `EDerSet f` (`EDerSet_mem`);
  * the three inequalities `0 ≤ u`, `|w_{j+1}| ≤ u`, `M(1+nu) < |w_0|` are manufactured from
    `posPoly_mem` (`leZeroCoord_mem`, `leCoord_mem`, `negLeCoord_mem`, `absGt_mem`);
  * intersecting and projecting (`projN_EInner`) produces `ESetD f M`, which is
    `c1Loc f ∩ {z | ∃ u ≥ 0, (∀ j, |∂_{j+1} f(z)| ≤ u) ∧ M(1+nu) < |∂₀ f(z)|}`;
  * the remaining conditions `z 0 ∈ (c,d)` and `Fin.tail z ∈ openCube n` are `Ω`-sets by
    `Work.WilG5.ltSet_mem`/`gtSet_mem`/`openCube_mem`.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.ESetDefs
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG4b.uniform_pullback_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4b
open WilkiesDesign WilkiesConjecture

/-! ## 1. `dDir` is the order-one iterated derivative -/

theorem dDir_eq_iteratedFDeriv {m : ℕ} (f : (Fin m → ℝ) → ℝ) (i : Fin m) (z : Fin m → ℝ) :
    dDir f i z = iteratedFDeriv ℝ 1 f z (fun _ : Fin 1 => Pi.single i 1) := by
  simp [dDir]

/-! ## 2. The derivative graphs of `SharpDeriv` at order one -/

theorem derivGraph_mem (S : SOMin) (hder : S.SharpDeriv) (m F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin m → ℝ) → ℝ) (i : Fin m),
        graphOf f ∈ S.Ω F0 D (m + 1) →
          derivGraph f i ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (m + 1) := by
  obtain ⟨a, b, hb⟩ := hder F0 m
  refine ⟨a, b, fun D f i hf => ?_⟩
  have h := hb D f hf 1 (fun _ : Fin 1 => i)
  have hset : derivGraph f i =
      {z : Fin (m + 1) → ℝ | Fin.init z ∈ interior {x | ContDiffAt ℝ 1 f x} ∧
        z (Fin.last m) = iteratedFDeriv ℝ 1 f (Fin.init z) (fun _ : Fin 1 => Pi.single i 1)} := by
    ext z
    simp only [derivGraph, c1Loc, dDir_eq_iteratedFDeriv]
  rw [hset]
  exact h

/-! ## 3. The derivative-set of the joint space is `Ω`-definable -/

theorem EDerSet_mem (S : SOMin) (hder : S.SharpDeriv) (n F0 : ℕ) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ),
      graphOf f ∈ S.Ω F0 D (n + 2) →
        EDerSet f ∈ S.Ω (F0 + K) (p.eval D) ((n + 1) + ((n + 1) + 1)) := by
  obtain ⟨a, b, hb⟩ := derivGraph_mem S hder (n + 1) F0
  obtain ⟨K1, p1, hp1⟩ := uniform_pullback_mem S ((n + 1) + 1) ((n + 1) + ((n + 1) + 1))
  refine ⟨a + K1 + 1, Polynomial.C (n + 1) * (p1.comp (Work.WilG1.psubst b 1)), ?_⟩
  intro D f hf
  have hc : ∀ i : Fin (n + 1),
      ECond f i ∈ S.Ω (a + K1) ((p1.comp (Work.WilG1.psubst b 1)).eval D)
        ((n + 1) + ((n + 1) + 1)) := by
    intro i
    have hdi : derivGraph f i ∈ S.Ω a ((Work.WilG1.psubst b 1).eval D) ((n + 1) + 1) := by
      rw [Work.WilG1.eval_psubst]
      exact hb D f i hf
    have h := hp1 (eIdx (n + 1) i) a ((Work.WilG1.psubst b 1).eval D) (derivGraph f i) hdi
    rw [← Polynomial.eval_comp] at h
    exact h
  have hinter := Work.WilG1.Omega.inter_mem (S := S) (D := D)
    (fun i : Fin (n + 1) => ECond f i) hc
  have hset : EDerSet f = ⋂ i : Fin (n + 1), ECond f i := rfl
  rw [hset]
  refine Work.WilG5.mem_mono hinter (F0 + (a + K1 + 1))
    ((Polynomial.C (n + 1) * (p1.comp (Work.WilG1.psubst b 1))).eval D) (by omega) le_rfl

/-! ## 4. Linear polynomial inequalities -/

theorem td_C_mul_X_le {N : ℕ} (a : ℝ) (i : Fin N) :
    ((MvPolynomial.C a : MvPolynomial (Fin N) ℝ) * MvPolynomial.X i).totalDegree ≤ 1 := by
  refine le_trans (Work.WilG5.td_mul_le _ _) ?_
  have h1 : (MvPolynomial.C a : MvPolynomial (Fin N) ℝ).totalDegree ≤ 0 :=
    Work.WilG5.td_C_le a
  have h2 : (MvPolynomial.X i : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le i
  omega

theorem td_const_add_CmulX_add_CmulX {N : ℕ} (r a b : ℝ) (i j : Fin N) :
    (MvPolynomial.C r + MvPolynomial.C a * MvPolynomial.X i +
      MvPolynomial.C b * MvPolynomial.X j : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · exact le_trans (Work.WilG5.td_C_le r) (Nat.zero_le 1)
    · exact td_C_mul_X_le a i
  · exact td_C_mul_X_le b j

theorem linPos_mem {N : ℕ} (S : SOMin) (P : MvPolynomial (Fin N) ℝ) (hP : P.totalDegree ≤ 1) :
    {x : Fin N → ℝ | 0 < MvPolynomial.eval x P} ∈ S.Ω (N + 4) 4 N :=
  Work.WilG5.mem_mono (posPoly_mem S P) (N + 4) 4 le_rfl (by omega)

theorem linNonpos_mem {N : ℕ} (S : SOMin) (P : MvPolynomial (Fin N) ℝ)
    (hP : P.totalDegree ≤ 1) :
    {x : Fin N → ℝ | MvPolynomial.eval x P ≤ 0} ∈ S.Ω (N + 5) 4 N := by
  have h := S.compl (linPos_mem S P hP)
  have he : ({x : Fin N → ℝ | 0 < MvPolynomial.eval x P})ᶜ
      = {x : Fin N → ℝ | MvPolynomial.eval x P ≤ 0} := by
    ext x; simp [not_lt]
  rw [he] at h
  exact Work.WilG5.mem_mono h (N + 5) 4 (by omega) le_rfl

/-- `{x | 0 ≤ x i}`. -/
theorem leZeroCoord_mem {N : ℕ} (S : SOMin) (D : ℕ) (i : Fin N) :
    {x : Fin N → ℝ | 0 ≤ x i} ∈ S.Ω (N + 5) ((Polynomial.C 4).eval D) N := by
  have h := linNonpos_mem S
    (MvPolynomial.C 0 + MvPolynomial.C (-1) * MvPolynomial.X i +
      MvPolynomial.C 0 * MvPolynomial.X i : MvPolynomial (Fin N) ℝ)
    (td_const_add_CmulX_add_CmulX 0 (-1) 0 i i)
  have hset : {x : Fin N → ℝ |
      MvPolynomial.eval x (MvPolynomial.C 0 + MvPolynomial.C (-1) * MvPolynomial.X i +
        MvPolynomial.C 0 * MvPolynomial.X i : MvPolynomial (Fin N) ℝ) ≤ 0}
      = {x : Fin N → ℝ | 0 ≤ x i} := by
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  simpa using h

/-- `{x | x i ≤ x j}`. -/
theorem leCoord_mem {N : ℕ} (S : SOMin) (D : ℕ) (i j : Fin N) :
    {x : Fin N → ℝ | x i ≤ x j} ∈ S.Ω (N + 5) ((Polynomial.C 4).eval D) N := by
  have h := linNonpos_mem S
    (MvPolynomial.C 0 + MvPolynomial.C 1 * MvPolynomial.X i +
      MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)
    (td_const_add_CmulX_add_CmulX 0 1 (-1) i j)
  have hset : {x : Fin N → ℝ |
      MvPolynomial.eval x (MvPolynomial.C 0 + MvPolynomial.C 1 * MvPolynomial.X i +
        MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ) ≤ 0}
      = {x : Fin N → ℝ | x i ≤ x j} := by
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  simpa using h

/-- `{x | -x i ≤ x j}`. -/
theorem negLeCoord_mem {N : ℕ} (S : SOMin) (D : ℕ) (i j : Fin N) :
    {x : Fin N → ℝ | -x i ≤ x j} ∈ S.Ω (N + 5) ((Polynomial.C 4).eval D) N := by
  have h := linNonpos_mem S
    (MvPolynomial.C 0 + MvPolynomial.C (-1) * MvPolynomial.X i +
      MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)
    (td_const_add_CmulX_add_CmulX 0 (-1) (-1) i j)
  have hset : {x : Fin N → ℝ |
      MvPolynomial.eval x (MvPolynomial.C 0 + MvPolynomial.C (-1) * MvPolynomial.X i +
        MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ) ≤ 0}
      = {x : Fin N → ℝ | -x i ≤ x j} := by
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  simpa using h

/-- `{x | M (1 + n x j) < |x i|}`. -/
theorem absGt_mem {N : ℕ} (S : SOMin) (D : ℕ) (i j : Fin N) (M : ℝ) (n : ℕ) :
    {x : Fin N → ℝ | M * (1 + n * x j) < |x i|} ∈ S.Ω (N + 4) ((Polynomial.C 8).eval D) N := by
  have h1 : {x : Fin N → ℝ | 0 < MvPolynomial.eval x
      (MvPolynomial.C (-M) + MvPolynomial.C 1 * MvPolynomial.X i +
        MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)} ∈
      S.Ω (N + 4) ((Polynomial.C 4).eval D) N := by
    simpa using linPos_mem S _
      (td_const_add_CmulX_add_CmulX (-M) 1 (-(M * n)) i j)
  have h2 : {x : Fin N → ℝ | 0 < MvPolynomial.eval x
      (MvPolynomial.C (-M) + MvPolynomial.C (-1) * MvPolynomial.X i +
        MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)} ∈
      S.Ω (N + 4) ((Polynomial.C 4).eval D) N := by
    simpa using linPos_mem S _
      (td_const_add_CmulX_add_CmulX (-M) (-1) (-(M * n)) i j)
  have h := Work.WilG1.Omega.union₂ (S := S) h1 h2
  have hset : {x : Fin N → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.C (-M) + MvPolynomial.C 1 * MvPolynomial.X i +
          MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)} ∪
      {x : Fin N → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.C (-M) + MvPolynomial.C (-1) * MvPolynomial.X i +
          MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)}
      = {x : Fin N → ℝ | M * (1 + n * x j) < |x i|} := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [lt_abs]
    constructor
    · rintro (h | h) <;> [left; right] <;> nlinarith
    · rintro (h | h) <;> [left; right] <;> nlinarith
  rw [hset] at h
  refine Work.WilG5.mem_mono h (N + 4) ((Polynomial.C 8).eval D) (by omega) ?_
  simp

/-! ## 5. The `Fin 4`-intersection gadget -/

theorem iInter_fin_four {α : Type*} (a b c d : Set α) :
    (⋂ i : Fin 4, (if i = 0 then a else if i = 1 then b else if i = 2 then c else d))
      = a ∩ b ∩ c ∩ d := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨⟨⟨by simpa using h 0, by simpa using h 1⟩, by simpa using h 2⟩, by simpa using h 3⟩
  · rintro ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ i
    fin_cases i <;> simp_all

/-! ## 5b. The projection equivalence -/

/-- Membership in the joint set, in terms of the coordinates of `Fin.append z y`. -/
theorem append_mem_EInner {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (M : ℝ)
    (z : Fin (n + 1) → ℝ) (y : Fin ((n + 1) + 1) → ℝ) :
    Fin.append z y ∈ EInner f M ↔
      (z ∈ c1Loc f ∧ ∀ i : Fin (n + 1), y i.castSucc = dDir f i z)
        ∧ 0 ≤ y (Fin.last (n + 1))
        ∧ (∀ j : Fin n, |y j.succ.castSucc| ≤ y (Fin.last (n + 1)))
        ∧ M * (1 + n * y (Fin.last (n + 1))) < |y (Fin.castSucc (0 : Fin (n + 1)))| := by
  have hEC : (∀ i : Fin (n + 1), (Fin.append z y) ∘ eIdx (n + 1) i ∈ derivGraph f i) ↔
      (z ∈ c1Loc f ∧ ∀ i : Fin (n + 1), y i.castSucc = dDir f i z) := by
    constructor
    · intro h
      refine ⟨?_, fun i => ?_⟩
      · have h0 := h 0
        rw [append_comp_eIdx (n + 1) 0 z y] at h0
        simp only [derivGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at h0
        exact h0.1
      · have hi := h i
        rw [append_comp_eIdx (n + 1) i z y] at hi
        simp only [derivGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hi
        exact hi.2
    · rintro ⟨hz, hy⟩ i
      rw [append_comp_eIdx (n + 1) i z y]
      simp only [derivGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hz, hy i⟩
  simp only [EInner, EDerSet, ECond, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hEC]
  simp only [append_wIdx, append_uIdx]
  tauto

/-- The projection of the joint set is `c1Loc f` together with the existence of a threshold
`u ≥ 0` dominating the `y`-partials and with `M (1 + n u) < |∂₀ f|`. -/
theorem ESetD_eq {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (M : ℝ) :
    ESetD f M = {z : Fin (n + 1) → ℝ | z ∈ c1Loc f ∧
      ∃ u : ℝ, 0 ≤ u ∧ (∀ j : Fin n, |dDir f j.succ z| ≤ u) ∧
        M * (1 + n * u) < |dDir f 0 z|} := by
  ext z
  simp only [ESetD, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩
    rw [append_mem_EInner] at hy
    obtain ⟨⟨hz, hyi⟩, hu0, huj, huc⟩ := hy
    refine ⟨hz, y (Fin.last (n + 1)), hu0, fun j => ?_, ?_⟩
    · rw [← hyi j.succ]; exact huj j
    · rw [← hyi 0]; exact huc
  · rintro ⟨hz, u, hu0, huj, huc⟩
    refine ⟨(Fin.snoc (fun i : Fin (n + 1) => dDir f i z) u : Fin ((n + 1) + 1) → ℝ), ?_⟩
    rw [append_mem_EInner]
    refine ⟨⟨hz, fun i => ?_⟩, ?_, ?_, ?_⟩
    · simp only [Fin.snoc_castSucc]
    · simpa only [Fin.snoc_last] using hu0
    · intro j
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact huj j
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact huc

/-! ## 6. The main theorem -/

theorem ESet_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) {n : ℕ} :
    ∀ F : ℕ, ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.graphOf f ∈ S.Ω F D (n + 2) →
        ∀ (c d M : ℝ), Work.WilG4b.ESet f c d M ∈ S.Ω (F + K) (p.eval D) (n + 1) := by
  intro F
  obtain ⟨Kd, pd, hd⟩ := EDerSet_mem S hder n F
  refine ⟨Kd + 4 * ((n + 1) + ((n + 1) + 1)) + 64 + ((n + 1) + 1) + 10,
    Polynomial.C 12 * (pd + Polynomial.C (8 * n + 40)), ?_⟩
  intro D f hf c d M
  have hDer : EDerSet f ∈ S.Ω (F + Kd) (pd.eval D) ((n + 1) + ((n + 1) + 1)) := hd D f hf
  -- common format and degree for the four pieces of the joint set
  let AF : ℕ := F + Kd + 4 * ((n + 1) + ((n + 1) + 1)) + 64
  let qc : Polynomial ℕ := pd + Polynomial.C (8 * n + 40)
  let Vu : Set (Fin ((n + 1) + ((n + 1) + 1)) → ℝ) := {x | 0 ≤ x (uIdx (n + 1))}
  let Vw : Set (Fin ((n + 1) + ((n + 1) + 1)) → ℝ) :=
    ⋂ j : Fin n, {x | |x (wIdx (n + 1) j.succ)| ≤ x (uIdx (n + 1))}
  let Vc : Set (Fin ((n + 1) + ((n + 1) + 1)) → ℝ) :=
    {x | M * (1 + n * x (uIdx (n + 1))) < |x (wIdx (n + 1) (0 : Fin (n + 1)))|}
  have hDer' : EDerSet f ∈ S.Ω AF (qc.eval D) ((n + 1) + ((n + 1) + 1)) := by
    refine Work.WilG5.mem_mono hDer AF (qc.eval D) ?_ ?_
    · dsimp only [AF]; omega
    · dsimp only [qc]; simp only [Polynomial.eval_add, Polynomial.eval_C]; omega
  have hVu : Vu ∈ S.Ω AF (qc.eval D) ((n + 1) + ((n + 1) + 1)) := by
    have h := leZeroCoord_mem (S := S) (N := (n + 1) + ((n + 1) + 1)) D (uIdx (n + 1))
    refine Work.WilG5.mem_mono h AF (qc.eval D) ?_ ?_
    · dsimp only [AF]; omega
    · dsimp only [qc]; simp only [Polynomial.eval_add, Polynomial.eval_C]; omega
  have hVw : Vw ∈ S.Ω AF (qc.eval D) ((n + 1) + ((n + 1) + 1)) := by
    have hsingle : ∀ j : Fin n,
        {x : Fin ((n + 1) + ((n + 1) + 1)) → ℝ |
          |x (wIdx (n + 1) j.succ)| ≤ x (uIdx (n + 1))} ∈
          S.Ω (((n + 1) + ((n + 1) + 1)) + 6) ((Polynomial.C 8).eval D)
            ((n + 1) + ((n + 1) + 1)) := by
      intro j
      have hA := leCoord_mem (S := S) (N := (n + 1) + ((n + 1) + 1)) D
        (wIdx (n + 1) j.succ) (uIdx (n + 1))
      have hB := negLeCoord_mem (S := S) (N := (n + 1) + ((n + 1) + 1)) D
        (wIdx (n + 1) j.succ) (uIdx (n + 1))
      have h := Work.WilG1.Omega.inter₂ (S := S) hA hB
      have he : {x : Fin ((n + 1) + ((n + 1) + 1)) → ℝ | x (wIdx (n + 1) j.succ) ≤ x (uIdx (n + 1))}
            ∩ {x : Fin ((n + 1) + ((n + 1) + 1)) → ℝ | -x (wIdx (n + 1) j.succ) ≤ x (uIdx (n + 1))}
          = {x : Fin ((n + 1) + ((n + 1) + 1)) → ℝ |
              |x (wIdx (n + 1) j.succ)| ≤ x (uIdx (n + 1))} := by
        ext x
        rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
          abs_le]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
      rw [he] at h
      refine Work.WilG5.mem_mono h _ ((Polynomial.C 8).eval D) (by omega) ?_
      simp only [Polynomial.eval_add, Polynomial.eval_C]
      omega
    have h := Work.WilG1.Omega.inter_mem (S := S) (D := D)
      (fun j : Fin n => {x : Fin ((n + 1) + ((n + 1) + 1)) → ℝ |
        |x (wIdx (n + 1) j.succ)| ≤ x (uIdx (n + 1))}) hsingle
    refine Work.WilG5.mem_mono h AF (qc.eval D) ?_ ?_
    · dsimp only [AF]; omega
    · dsimp only [qc]; simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      omega
  have hVc : Vc ∈ S.Ω AF (qc.eval D) ((n + 1) + ((n + 1) + 1)) := by
    have h := absGt_mem (S := S) (N := (n + 1) + ((n + 1) + 1)) D
      (wIdx (n + 1) (0 : Fin (n + 1))) (uIdx (n + 1)) M n
    refine Work.WilG5.mem_mono h AF (qc.eval D) ?_ ?_
    · dsimp only [AF]; omega
    · dsimp only [qc]; simp only [Polynomial.eval_add, Polynomial.eval_C]; omega
  -- the joint set
  have hfam : ∀ i : Fin 4,
      (if i = 0 then EDerSet f else if i = 1 then Vu else if i = 2 then Vw else Vc) ∈
        S.Ω AF (qc.eval D) ((n + 1) + ((n + 1) + 1)) := by
    intro i
    fin_cases i
    · simpa using hDer'
    · simpa using hVu
    · simpa using hVw
    · simpa using hVc
  have hInner := Work.WilG1.Omega.inter_mem (S := S) (D := D)
    (fun i : Fin 4 =>
      if i = 0 then EDerSet f else if i = 1 then Vu else if i = 2 then Vw else Vc) hfam
  rw [iInter_fin_four] at hInner
  have hInner' : EInner f M ∈ S.Ω (AF + 1) ((Polynomial.C 4 * qc).eval D)
      ((n + 1) + ((n + 1) + 1)) := hInner
  -- projecting out the `w`-block and `u`
  have hProj : ESetD f M ∈ S.Ω (AF + 1 + ((n + 1) + 1)) ((Polynomial.C 4 * qc).eval D) (n + 1) :=
    Work.WilG5.projN_mem (S := S) (n := n + 1) ((n + 1) + 1) (AF + 1)
      ((Polynomial.C 4 * qc).eval D) hInner'
  -- the two elementary conditions
  have hA1 : {z : Fin (n + 1) → ℝ | c < z 0} ∈
      S.Ω (4 * (n + 1) + 20) ((Polynomial.C 8).eval D) (n + 1) := by
    simpa using (Work.WilG5.ltSet_mem (S := S) (n := n + 1) (0 : Fin (n + 1)) c)
  have hA2 : {z : Fin (n + 1) → ℝ | z 0 < d} ∈
      S.Ω (4 * (n + 1) + 20) ((Polynomial.C 8).eval D) (n + 1) := by
    simpa using (Work.WilG5.gtSet_mem (S := S) (n := n + 1) (0 : Fin (n + 1)) d)
  have hA : {z : Fin (n + 1) → ℝ | z 0 ∈ Set.Ioo c d} ∈
      S.Ω (4 * (n + 1) + 21) ((Polynomial.C 8 + Polynomial.C 8).eval D) (n + 1) := by
    have h := Work.WilG1.Omega.inter₂ (S := S) hA1 hA2
    have he : {z : Fin (n + 1) → ℝ | c < z 0} ∩ {z : Fin (n + 1) → ℝ | z 0 < d}
        = {z : Fin (n + 1) → ℝ | z 0 ∈ Set.Ioo c d} := by
      ext z; simp [Set.mem_Ioo]
    rw [he] at h
    refine Work.WilG5.mem_mono h (4 * (n + 1) + 21) _ ?_ le_rfl
    omega
  have hB : {z : Fin (n + 1) → ℝ | Fin.tail z ∈ openCube n} ∈
      S.Ω (4 * n + 25) ((Polynomial.C (16 * n + 16)).eval D) (n + 1) := by
    have h := S.prod_left (Work.WilG5.openCube_mem (S := S) (n := n))
    refine Work.WilG5.mem_mono h (4 * n + 25) ((Polynomial.C (16 * n + 16)).eval D) ?_ ?_
    · omega
    · simp
  -- raise `A` and `B` to the format/degree of `ESetD`
  have hA' : {z : Fin (n + 1) → ℝ | z 0 ∈ Set.Ioo c d} ∈
      S.Ω (AF + 1 + ((n + 1) + 1)) ((Polynomial.C 4 * qc).eval D) (n + 1) := by
    refine Work.WilG5.mem_mono hA (AF + 1 + ((n + 1) + 1)) ((Polynomial.C 4 * qc).eval D) ?_ ?_
    · dsimp only [AF]; omega
    · dsimp only [qc]
      simp only [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C]
      omega
  have hB' : {z : Fin (n + 1) → ℝ | Fin.tail z ∈ openCube n} ∈
      S.Ω (AF + 1 + ((n + 1) + 1)) ((Polynomial.C 4 * qc).eval D) (n + 1) := by
    refine Work.WilG5.mem_mono hB (AF + 1 + ((n + 1) + 1)) ((Polynomial.C 4 * qc).eval D) ?_ ?_
    · dsimp only [AF]; omega
    · dsimp only [qc]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      omega
  have hAB := Work.WilG1.Omega.inter₂ (S := S) hA' hB'
  have hfinal := Work.WilG1.Omega.inter₂ (S := S) hAB hProj
  have hsetEq : ESet f c d M =
      {z : Fin (n + 1) → ℝ | z 0 ∈ Set.Ioo c d} ∩ {z : Fin (n + 1) → ℝ | Fin.tail z ∈ openCube n}
        ∩ ESetD f M := by
    ext z
    simp only [ESet, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [ESetD_eq f M]
    simp only [Set.mem_ofPred_eq]
    tauto
  rw [hsetEq]
  refine Work.WilG5.mem_mono hfinal
    (F + (Kd + 4 * ((n + 1) + ((n + 1) + 1)) + 64 + ((n + 1) + 1) + 10))
    ((Polynomial.C 12 * (pd + Polynomial.C (8 * n + 40))).eval D) ?_ ?_
  · dsimp only [AF]; omega
  · dsimp only [qc]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega

end Work.WilG4b
