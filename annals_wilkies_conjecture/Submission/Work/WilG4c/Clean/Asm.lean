import Mathlib
import Submission.Work.WilG4c.Clean.AsmAux
import Submission.Work.WilG4c.fibreSet_mem
import Submission.Work.WilG4c.exists_count_poly

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-- BNZ §5.5 assembly, conditional on the "cores" hypothesis on the fibre non-`C^r` locus.
Nine-step recipe with all pieces already available (`Submission/Work/WilG4c/STEPCLEAN_NOTES.md`
§2f, header of `Submission/Work/WilG4c/StepCleanAsm.lean`): `StepCellEngineFibre` supplies the
engine; `hcores` gives the cores `A_i` and their union `W`; `S.SharpCD` applied to the *family*
`{A_i j}_{i,j} ∪ {lift of inCubeSet}` (feed the family, NOT the union: unioning would put `k`
into the cell degree and hence into the chart degree) gives the decomposition `C`; apply the
engine per cell `κ ∈ C` that is inside the cube and disjoint from every `A_i j`, with
`Λ_κ := {l | ∃ y, Fin.append l y ∈ κ}`; the fibre-smoothness hypothesis comes from
`Work.WilG4c.fibreSmooth_of_not_mem` plus `NormLeOneDef`; extend the chart families from `Λ_κ`
to `Λ` with the constant `(1/2,…,1/2)` via `Work.WilG4c.PerLambda.ChartsOK_extends` (the
`Ω`-bound of the modified charts is `Work.WilG4c.ite_graph_mem4`, format `+4`, degree `*4`);
union the pieces and bound the count by a polynomial in `D,r,k,-log ε` using
`Work.WilG4c.polyCountEval_comp4`; the cover uses `Work.WilG4c.escape_of_interior_empty` and
`LipOnCube F 1`. -/
theorem FLemPOfFibreCores (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (n p : ℕ) (hn : 1 ≤ n)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n)
    (hcores : ∀ F0 : ℕ, ∃ (K M : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        ∃ A : Fin M → Set (Fin (p + (n + 1)) → ℝ),
          (∀ j, A j ∈ S.Ω (F0 + K) (MvPolynomial.eval ![D, r] b) (p + (n + 1))) ∧
          (∀ l : Fin p → ℝ,
            interior {z : Fin (n + 1) → ℝ | Fin.append l z ∈ ⋃ j, A j} = ∅) ∧
          (∀ l : Fin p → ℝ,
            {z : Fin (n + 1) → ℝ | ¬ ContDiffAt ℝ r (fun z => f l z) z} ⊆
              {z : Fin (n + 1) → ℝ | Fin.append l z ∈ ⋃ j, A j})) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLipDef p n) := by
  classical
  intro F0
  obtain ⟨Kc, Mc, bcore, hcore⟩ := hcores F0
  set N : ℕ := n + 1 with hN
  obtain ⟨Kf, hKf⟩ := fibreSet_mem S p N
  set Fcd : ℕ := max (F0 + Kc) (p + N + 4) with hFcd
  obtain ⟨a_cd, b_cd, c_cd, hCD⟩ := hcd Fcd (p + N)
  set F0E : ℕ := max F0 a_cd with hF0E
  obtain ⟨aE, bE, cE, hE⟩ := StepCellEngineFibre S n p hn ih F0E
  obtain ⟨Kp, hKp⟩ := paramSet_mem S p N
  set aΛ : ℕ := a_cd + Kp with haΛ
  set FtΛ : ℕ := max (aΛ + (p + N)) ((p + N) + p) + 1 + p + (p + N) with hFtΛ
  set Ft : ℕ := max (max aE FtΛ) (p + N + 1) with hFt
  set Bcd : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C Mc * bcore + MvPolynomial.C (6 * N) with hBcd
  obtain ⟨Bcdp, hBcdp⟩ := exists_poly_eval_poly c_cd Bcd 0
  set bstep : MvPolynomial (Fin 2) ℕ := Bcd + Bcdp with hbstep
  obtain ⟨Bdeg, hBdeg⟩ := exists_poly_shift2 bE bstep 0
  obtain ⟨Blam, hBlam⟩ := exists_poly_eval_poly c_cd Bcd 2
  set bfin : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C 4 * (Bdeg + Blam + MvPolynomial.C 1) with hbfin
  obtain ⟨cf, hcf⟩ := exists_count_poly b_cd cE Bcd bstep 1
  refine ⟨Ft + 4, bfin, cf, ?_⟩
  intro D r k ε hε0 hε1 Λ F hP hΩ hval
  -- degree bookkeeping
  set Dcd : ℕ := MvPolynomial.eval ![D, r] Bcd with hDcd
  set DE : ℕ := D + MvPolynomial.eval ![D, r] bstep with hDE
  set Dt : ℕ := max (max (MvPolynomial.eval ![DE, r] bE) (c_cd.eval Dcd + 2)) 1 with hDt
  have hε2 : 0 < ε / 2 := by linarith
  have hε2' : ε / 2 < 1 := by linarith
  have hstepEval : MvPolynomial.eval ![D, r] bstep
      = MvPolynomial.eval ![D, r] Bcd + MvPolynomial.eval ![D, r] Bcdp := by
    rw [hbstep, MvPolynomial.eval_add]
  -- ## the cores of each family member
  have hcore_i : ∀ i : Fin k, ∃ A : Fin Mc → Set (Fin (p + N) → ℝ),
      (∀ j, A j ∈ S.Ω (F0 + Kc) (MvPolynomial.eval ![D, r] bcore) (p + N)) ∧
      (∀ l : Fin p → ℝ, interior {z : Fin N → ℝ | Fin.append l z ∈ ⋃ j, A j} = ∅) ∧
      (∀ l : Fin p → ℝ, {z : Fin N → ℝ | ¬ ContDiffAt ℝ r (F i l) z} ⊆
        {z : Fin N → ℝ | Fin.append l z ∈ ⋃ j, A j}) :=
    fun i => hcore D r (F i) (hΩ i)
  choose Acore hAcore using hcore_i
  set Wset : Fin k → Set (Fin (p + N) → ℝ) := fun i => ⋃ j : Fin Mc, Acore i j with hWset
  have hWΩ : ∀ i : Fin k,
      Wset i ∈ S.Ω (F0 + Kc) (Mc * MvPolynomial.eval ![D, r] bcore) (p + N) := by
    intro i
    have h := S.union (D := fun _ : Fin Mc => MvPolynomial.eval ![D, r] bcore)
      (A := Acore i) (fun j => (hAcore i).1 j)
    have hsum : (∑ _ : Fin Mc, MvPolynomial.eval ![D, r] bcore)
        = Mc * MvPolynomial.eval ![D, r] bcore := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [hsum] at h
    simpa [hWset] using h
  have hBcdEval : Dcd = Mc * MvPolynomial.eval ![D, r] bcore + 6 * N := by
    rw [hDcd, hBcd]
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hcoreCD : ∀ i : Fin k, Wset i ∈ S.Ω Fcd Dcd (p + N) := by
    intro i
    refine Work.WilG1.Omega.mono (hWΩ i) ?_ ?_
    · rw [hFcd]; omega
    · rw [hBcdEval]; omega
  have hcubeCD : inCubeSet p N ∈ S.Ω Fcd Dcd (p + N) := by
    refine Work.WilG1.Omega.mono (clean_inCubeSet_mem S p N) ?_ ?_
    · rw [hFcd]; omega
    · rw [hBcdEval]; omega
  -- ## the sharp cell decomposition
  set X : Fin (k + 1) → Set (Fin (p + N) → ℝ) := Fin.snoc Wset (inCubeSet p N) with hX
  have hXΩ : ∀ t : Fin (k + 1), X t ∈ S.Ω Fcd Dcd (p + N) := by
    intro t
    refine Fin.lastCases ?_ (fun i => ?_) t
    · simp only [hX, Fin.snoc_last]; exact hcubeCD
    · simp only [hX, Fin.snoc_castSucc]; exact hcoreCD i
  obtain ⟨C, hdec, hsep, hcardC, hcellΩ'⟩ := hCD Dcd (k + 1) X hXΩ
  have hsepCube : ∀ κ ∈ C, κ ⊆ inCubeSet p N ∨ Disjoint κ (inCubeSet p N) := by
    intro κ hκ
    have h := hsep (Fin.last k) κ hκ
    simpa only [hX, Fin.snoc_last] using h
  have hsepW : ∀ i : Fin k, ∀ κ ∈ C, κ ⊆ Wset i ∨ Disjoint κ (Wset i) := by
    intro i κ hκ
    have h := hsep i.castSucc κ hκ
    simpa only [hX, Fin.snoc_castSucc] using h
  -- ## the fibre-thinness of the union of the cores
  set W : Set (Fin (p + N) → ℝ) := ⋃ i : Fin k, Wset i with hWdef
  have hthin : ∀ l : Fin p → ℝ,
      interior {z : Fin N → ℝ | Fin.append l z ∈ W} = ∅ := by
    intro l
    set Y : Fin k → Set (Fin N → ℝ) := fun i => {z : Fin N → ℝ | Fin.append l z ∈ Wset i}
      with hYdef
    have hYΩ : ∀ i : Fin k, Y i ∈ S.Ω ((F0 + Kc) + Kf)
        ((Mc * MvPolynomial.eval ![D, r] bcore) + Kf) N := by
      intro i
      exact hKf (F0 + Kc) (Mc * MvPolynomial.eval ![D, r] bcore) (Wset i) l (hWΩ i)
    have hYthin : ∀ i : Fin k, interior (Y i) = ∅ := by
      intro i
      have h := (hAcore i).2.1 l
      simpa only [hYdef, hWset] using h
    have h := Work.WilG1.Cell.thin_union (S := S) hcd k ((F0 + Kc) + Kf) Polynomial.X
      ((Mc * MvPolynomial.eval ![D, r] bcore) + Kf) Y (fun i => by simpa using hYΩ i) hYthin
    have hset : (⋃ i : Fin k, Y i) = {z : Fin N → ℝ | Fin.append l z ∈ W} := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, hYdef, hWdef]
    rwa [hset] at h
  -- ## the chart family of one good cell
  have hgood_engine : ∀ κ ∈ C, κ ⊆ inCubeSet p N → (∀ i : Fin k, Disjoint κ (Wset i)) →
      ∃ Ψ : Finset (ChartTuple p N),
        (Ψ.card : ℝ) ≤ |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ),
            (r : ℝ), (1 : ℝ), -Real.log (ε / 2)] cE| ∧
        ChartsOK S (Ft + 4) (MvPolynomial.eval ![D, r] bfin) r Λ F Ψ ∧
        (∀ l ∈ Λ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ →
          ∃ φ ∈ Ψ, ∃ t ∈ openCube N, ∀ j : Fin N, |φ j l t - y j| < ε / 2) := by
    intro κ hκC hκcube hκdisj
    set Λκ : Set (Fin p → ℝ) := {l | ∃ y : Fin N → ℝ, Fin.append l y ∈ κ} with hΛκ
    have hΛκΩ : Λκ ∈ S.Ω aΛ (c_cd.eval Dcd) p := by
      have h := hKp a_cd (c_cd.eval Dcd) κ (hcellΩ' κ hκC)
      rw [← haΛ] at h
      simpa only [hΛκ] using h
    set P : Set (Fin (p + N) → ℝ) :=
      {w | (fun i : Fin p => w (Fin.castAdd N i)) ∈ Λκ} with hPdef
    have hPΩ : P ∈ S.Ω FtΛ (c_cd.eval Dcd + 2) (p + N) := by
      have h := Work.WilG0.substSet_mem (S := S) hΛκΩ (p + N) (Fin.castAdd N)
      simpa only [hPdef, Function.comp_def, hFtΛ] using h
    have hΩE : ∀ i : Fin k, famGraph (F i) ∈ S.Ω F0E DE (p + N + 1) := by
      intro i
      refine Work.WilG1.Omega.mono (hΩ i) ?_ ?_
      · rw [hF0E]; omega
      · rw [hDE]; omega
    have hcellΩE : ∀ κ' ∈ C, κ' ∈ S.Ω F0E DE (p + N) := by
      intro κ' hκ'
      refine Work.WilG1.Omega.mono (hcellΩ' κ' hκ') ?_ ?_
      · rw [hF0E]; omega
      · rw [hDE, hstepEval, hDcd]
        have h1 : c_cd.eval (MvPolynomial.eval ![D, r] Bcd) ≤ MvPolynomial.eval ![D, r] Bcdp := by
          have := hBcdp D r
          simpa using this
        omega
    have hvalΛ : ValuesIn01 (Λ ∩ Λκ) F := fun i l hl x hx => hval i l hl.1 x hx
    have hfib : ∀ i : Fin k, ∀ l ∈ Λ ∩ Λκ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ →
        ContDiffAt ℝ r (F i l) y ∧
          ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m (F i l) y‖ ≤ 1 := by
      intro i l hl y hy
      have hnot : ∀ i' : Fin k, Fin.append l y ∉ Wset i' :=
        fun i' hmem => (Set.disjoint_left.mp (hκdisj i')) hy hmem
      exact fibreSmooth_of_not_mem' (Wf := Wset) hP.2.2 (clean_mem_openCube_of_mem_inCubeSet hκcube hy)
        (fun i' => (hAcore i').2.2 l) hnot i
    obtain ⟨Ψ₀, hΨ₀card, hΨ₀ok, hΨ₀cov⟩ :=
      hE DE r k (Λ ∩ Λκ) F C κ hΩE hvalΛ hP.2.1 hdec hcellΩE hκC hκcube hfib
        (fun l hl => hl.2) (ε / 2) hε2 hε2'
    set mod : ChartTuple p N → ChartTuple p N :=
      fun φ j l t => if l ∈ Λκ then φ j l t else (1 / 2 : ℝ) with hmoddef
    have hmod : ∀ φ j l, l ∈ Λκ → ∀ t : Fin N → ℝ, mod φ j l t = φ j l t := by
      intro φ j l hl t; simp only [hmoddef, hl, ↓reduceIte]
    have hmodc : ∀ φ j l, l ∉ Λκ → ∀ t : Fin N → ℝ,
        mod φ j l t = (fun _ : Fin N => (1 / 2 : ℝ)) j := by
      intro φ j l hl t; simp only [hmoddef, hl, ↓reduceIte]
    have h4Dt : 4 * Dt ≤ MvPolynomial.eval ![D, r] bfin := by
      have h1 : MvPolynomial.eval ![DE, r] bE ≤ MvPolynomial.eval ![D, r] Bdeg := by
        have h := hBdeg D r
        have hp : (![DE, r] : Fin 2 → ℕ) = ![D + MvPolynomial.eval ![D, r] bstep + 0, r] := by
          funext i; fin_cases i <;> simp [hDE]
        rwa [← hp] at h
      have h2 : c_cd.eval Dcd + 2 ≤ MvPolynomial.eval ![D, r] Blam := by
        have h := hBlam D r
        rwa [← hDcd] at h
      have hmax1 : max (max (MvPolynomial.eval ![DE, r] bE) (c_cd.eval Dcd + 2)) 1
          ≤ MvPolynomial.eval ![D, r] Bdeg + MvPolynomial.eval ![D, r] Blam + 1 := by
        refine max_le (max_le ?_ ?_) ?_ <;> omega
      have h3 : MvPolynomial.eval ![D, r] bfin
          = 4 * (MvPolynomial.eval ![D, r] Bdeg + MvPolynomial.eval ![D, r] Blam + 1) := by
        simp only [hbfin, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_add]
          <;> ring
      rw [hDt, h3]
      exact Nat.mul_le_mul_left 4 hmax1
    have hmodΩ : ∀ φ ∈ Ψ₀, ∀ j : Fin N,
        famGraph ((mod φ) j) ∈ S.Ω (Ft + 4) (MvPolynomial.eval ![D, r] bfin) (p + N + 1) := by
      intro φ hφ j
      have hφΩ : graphOf (flatFun (φ j)) ∈ S.Ω aE (MvPolynomial.eval ![DE, r] bE) (p + N + 1) := by
        have h := (hΨ₀ok φ hφ).1 j
        rwa [famGraph_eq_graphOf_flatFun] at h
      have hft : graphOf (flatFun (φ j)) ∈ S.Ω Ft Dt (p + N + 1) :=
        Work.WilG1.Omega.mono hφΩ (by rw [hFt]; omega) (by rw [hDt]; omega)
      have hPmem : P ∈ S.Ω Ft Dt (p + N) :=
        Work.WilG1.Omega.mono hPΩ (by rw [hFt]; omega) (by rw [hDt]; omega)
      have hconst : graphOf (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ)) ∈ S.Ω Ft Dt (p + N + 1) :=
        Work.WilG1.Omega.mono (clean_graphOf_const_mem S (p + N) (1 / 2))
          (by rw [hFt]; omega) (by rw [hDt]; omega)
      have hmain := clean_ite_graph_mem4 S (p + N) Ft Dt hPmem hft hconst
      have hseteq : graphOf (Work.WilG4a.iteFun P (flatFun (φ j))
            (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ))) = famGraph ((mod φ) j) := by
        rw [famGraph_eq_graphOf_flatFun]
        apply congrArg graphOf
        funext z
        simp only [Work.WilG4a.iteFun, flatFun, hmoddef, hPdef]
        by_cases h : (fun i : Fin p => z (Fin.castAdd N i)) ∈ Λκ <;> simp [h]
      rw [hseteq] at hmain
      exact Work.WilG1.Omega.mono hmain le_rfl h4Dt
    obtain ⟨Φκ, hΦκmem, hΦκcard, hΦκOK⟩ :=
      ChartsOK_extends' (S := S) (Λ := Λ) (Λ' := Λκ)
        (c := fun _ : Fin N => (1 / 2 : ℝ)) (clean_const_half_mem_openCube N) hval mod
        hmod hmodc hmodΩ
        (fun φ hφ l hl hlκ => (hΨ₀ok φ hφ).2 l ⟨hl, hlκ⟩)
    refine ⟨Φκ, ?_, hΦκOK, ?_⟩
    · calc (Φκ.card : ℝ) ≤ (Ψ₀.card : ℝ) := by exact_mod_cast hΦκcard
        _ ≤ MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ), (r : ℝ),
              (1 : ℝ), -Real.log (ε / 2)] cE := hΨ₀card
        _ ≤ |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ), (r : ℝ),
              (1 : ℝ), -Real.log (ε / 2)] cE| := le_abs_self _
    · intro l hl y hy
      obtain ⟨φ, hφ, t, ht, hbd⟩ := hΨ₀cov l ⟨hl, ⟨y, hy⟩⟩ y hy
      refine ⟨mod φ, hΦκmem φ hφ, t, ht, fun j => ?_⟩
      rw [hmod φ j l ⟨y, hy⟩ t]
      exact hbd j
  -- ## assembling over the cells
  set Ψf : Set (Fin (p + N) → ℝ) → Finset (ChartTuple p N) := fun κ =>
    if h : κ ∈ C ∧ κ ⊆ inCubeSet p N ∧ ∀ i : Fin k, Disjoint κ (Wset i)
      then (hgood_engine κ h.1 h.2.1 h.2.2).choose else ∅ with hΨf
  have hΨf_spec : ∀ κ (hκC : κ ∈ C) (hc : κ ⊆ inCubeSet p N)
      (hd : ∀ i : Fin k, Disjoint κ (Wset i)),
      ((Ψf κ).card : ℝ) ≤ |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ),
          (r : ℝ), (1 : ℝ), -Real.log (ε / 2)] cE| ∧
      ChartsOK S (Ft + 4) (MvPolynomial.eval ![D, r] bfin) r Λ F (Ψf κ) ∧
      (∀ l ∈ Λ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ →
        ∃ φ ∈ Ψf κ, ∃ t ∈ openCube N, ∀ j : Fin N, |φ j l t - y j| < ε / 2) := by
    intro κ hκC hc hd
    have hspec : Ψf κ = (hgood_engine κ hκC hc hd).choose := by
      rw [hΨf]
      exact dif_pos ⟨hκC, hc, hd⟩
    rw [hspec]
    exact (hgood_engine κ hκC hc hd).choose_spec
  set Φ : Finset (ChartTuple p N) := C.biUnion Ψf with hΦdef
  have hΦcard : (Φ.card : ℝ) ≤
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cf := by
    have hbnd : (Φ.card : ℝ) ≤
        (MvPolynomial.eval ![(MvPolynomial.eval ![D, r] Bcd), k * 1 + 1] b_cd : ℝ) *
          |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ), (r : ℝ),
            (1 : ℝ), -Real.log (ε / 2)] cE| := by
      have h1 : Φ.card ≤ ∑ κ ∈ C, (Ψf κ).card := by
        rw [hΦdef]; exact Finset.card_biUnion_le
      have h2 : ∀ κ ∈ C, ((Ψf κ).card : ℝ) ≤
          |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ), (r : ℝ),
            (1 : ℝ), -Real.log (ε / 2)] cE| := by
        intro κ hκ
        by_cases hg : κ ⊆ inCubeSet p N ∧ ∀ i : Fin k, Disjoint κ (Wset i)
        · exact (hΨf_spec κ hκ hg.1 hg.2).1
        · have hnil : Ψf κ = ∅ := by
            rw [hΨf]
            exact dif_neg (fun h => hg ⟨h.2.1, h.2.2⟩)
          rw [hnil, Finset.card_empty]
          simp
      have h3 : (((∑ κ ∈ C, (Ψf κ).card : ℕ)) : ℝ) ≤ (C.card : ℝ) *
          |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ), (r : ℝ),
            (1 : ℝ), -Real.log (ε / 2)] cE| := by
        rw [Nat.cast_sum]
        calc ∑ κ ∈ C, ((Ψf κ).card : ℝ)
            ≤ ∑ _κ ∈ C, |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ),
                (r : ℝ), (1 : ℝ), -Real.log (ε / 2)] cE| :=
              Finset.sum_le_sum (fun κ hκ => h2 κ hκ)
          _ = (C.card : ℝ) * |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ),
                (r : ℝ), (1 : ℝ), -Real.log (ε / 2)] cE| := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have h4 : (C.card : ℝ) ≤
          (MvPolynomial.eval ![(MvPolynomial.eval ![D, r] Bcd), k * 1 + 1] b_cd : ℝ) := by
        have h := hcardC
        rw [hDcd] at h
        have h' : MvPolynomial.eval ![MvPolynomial.eval ![D, r] Bcd, k + 1] b_cd
            = MvPolynomial.eval ![(MvPolynomial.eval ![D, r] Bcd), k * 1 + 1] b_cd := by
          simp only [Nat.mul_one]
        rw [h'] at h
        exact_mod_cast h
      calc (Φ.card : ℝ) ≤ (((∑ κ ∈ C, (Ψf κ).card : ℕ)) : ℝ) := by exact_mod_cast h1
        _ ≤ (C.card : ℝ) * |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ),
              (r : ℝ), (1 : ℝ), -Real.log (ε / 2)] cE| := h3
        _ ≤ (MvPolynomial.eval ![(MvPolynomial.eval ![D, r] Bcd), k * 1 + 1] b_cd : ℝ) *
              |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] bstep : ℕ) : ℝ), (r : ℝ),
                (1 : ℝ), -Real.log (ε / 2)] cE| :=
            mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    refine le_trans hbnd ?_
    simpa only [Nat.mul_one] using hcf D r k ε hε0 hε1
  have hΦOK : ChartsOK S (Ft + 4) (MvPolynomial.eval ![D, r] bfin) r Λ F Φ := by
    intro φ hφ
    rw [hΦdef] at hφ
    obtain ⟨κ, hκC, hφκ⟩ := Finset.mem_biUnion.mp hφ
    by_cases hg : κ ⊆ inCubeSet p N ∧ ∀ i : Fin k, Disjoint κ (Wset i)
    · exact (hΨf_spec κ hκC hg.1 hg.2).2.1 φ hφκ
    · have hnil : Ψf κ = ∅ := by
        rw [hΨf]
        exact dif_neg (fun h => hg ⟨h.2.1, h.2.2⟩)
      rw [hnil] at hφκ
      exact absurd hφκ (Finset.notMem_empty φ)
  have hΦcov : ∀ l ∈ Λ, ∀ x ∈ openCube N, ∃ φ ∈ Φ, ∃ t ∈ openCube N,
      ∀ i : Fin k, |F i l (fun j => φ j l t) - F i l x| < ε := by
    intro l hl x hx
    obtain ⟨y, hy, hydist, hyW⟩ :=
      escape_of_interior_empty' (hthin l) hx (by linarith : (0 : ℝ) < ε / 2)
    obtain ⟨κ, hκC, hyκ⟩ := Work.WilG1.Cell.exists_mem_of_cylDecomp hdec (Fin.append l y)
    have hcubeκ : κ ⊆ inCubeSet p N := by
      rcases hsepCube κ hκC with h | h
      · exact h
      · exfalso
        have hycube : Fin.append l y ∈ inCubeSet p N := by
          simp only [inCubeSet, Set.mem_ofPred_eq, openCube, Set.mem_ofPred_eq]
          intro j
          rw [Fin.append_right]
          exact hy j
        exact (Set.disjoint_left.mp h) hyκ hycube
    have hdisjκ : ∀ i : Fin k, Disjoint κ (Wset i) := by
      intro i
      rcases hsepW i κ hκC with h | h
      · exfalso
        exact hyW (Set.mem_iUnion.mpr ⟨i, h hyκ⟩)
      · exact h
    obtain ⟨φ, hφ, t, ht, hbd⟩ := (hΨf_spec κ hκC hcubeκ hdisjκ).2.2 l hl y hyκ
    refine ⟨φ, ?_, t, ht, fun i => ?_⟩
    · rw [hΦdef]; exact Finset.mem_biUnion.mpr ⟨κ, hκC, hφ⟩
    · have hpt : (fun j => φ j l t) ∈ openCube N :=
          (((hΨf_spec κ hκC hcubeκ hdisjκ).2.1 φ hφ).2 l hl).1 t ht
      have hd1 : dist (fun j => φ j l t) y < ε / 2 := by
        rw [dist_pi_lt_iff (by linarith)]
        intro j
        simpa [Real.dist_eq] using hbd j
      have hl1 := hP.2.1 i l (fun j => φ j l t) y hpt hy
      have hl2 := hP.2.1 i l y x hy hx
      rw [one_mul] at hl1 hl2
      have htri : |F i l (fun j => φ j l t) - F i l x|
          ≤ |F i l (fun j => φ j l t) - F i l y| + |F i l y - F i l x| := by
        have h := abs_add_le (F i l (fun j => φ j l t) - F i l y) (F i l y - F i l x)
        have heq : (F i l (fun j => φ j l t) - F i l y) + (F i l y - F i l x)
            = F i l (fun j => φ j l t) - F i l x := by ring
        rwa [heq] at h
      linarith
  exact ⟨Φ, hΦcard, hΦOK, hΦcov⟩

end Work.WilG4c

/-! ### Alias

The file (and most of the `Submission/Work/WilG4c/` area) spells its namespace
`Work.WilG4c`, while the task statement and the delegation machinery refer to the same
declarations as `Work.WilkG4c.*`.  For convenience we record the same theorem under that
alternative spelling, so that either name can be used by a consumer of this module.  This is a
plain synonym: it is *proved* by applying the theorem above. -/

namespace Work.WilkG4c

/-- Alias of `Work.WilG4c.FLemPOfFibreCores` (same statement, alternative namespace spelling). -/
theorem FLemPOfFibreCores (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (n p : ℕ) (hn : 1 ≤ n)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n)
    (hcores : ∀ F0 : ℕ, ∃ (K M : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        ∃ A : Fin M → Set (Fin (p + (n + 1)) → ℝ),
          (∀ j, A j ∈ S.Ω (F0 + K) (MvPolynomial.eval ![D, r] b) (p + (n + 1))) ∧
          (∀ l : Fin p → ℝ,
            interior {z : Fin (n + 1) → ℝ | Fin.append l z ∈ ⋃ j, A j} = ∅) ∧
          (∀ l : Fin p → ℝ,
            {z : Fin (n + 1) → ℝ | ¬ ContDiffAt ℝ r (fun z => f l z) z} ⊆
              {z : Fin (n + 1) → ℝ | Fin.append l z ∈ ⋃ j, A j})) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLipDef p n) :=
  Work.WilG4c.FLemPOfFibreCores S hcd n p hn ih hcores

end Work.WilkG4c
