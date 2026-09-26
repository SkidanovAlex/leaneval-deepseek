import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.OrbitKeysDefs
import Submission.Work.PTCert.OrbitKeys.keyWordLprod
import Submission.Work.PTCert.OrbitKeys.orbitConjPos
import Submission.Work.PTCert.OrbitKeys.orbitConjZero
import Submission.Work.PTCert.OrbitKeys.cardFiber

/-!
# `Work.PTCert.orbitKeys` — the orbit decomposition down to the group keys

Step **(J)** of `Submission/Work/PTCert/Glue3.lean`: for every value table `pv`,

`conjAvg Sg (gramForm fE (Pmat pv)) = conjAvg Sg (Σ_{r<18} Σ_{g<ngE r} multE (keyOf r g) * pv (keyOf r g) • of (lprod 5 (keyWord r g)))`.

Ingredients (all imported from `Submission/Work/PTCert/OrbitKeys/*`):
* `OrbitDecomp` (`hOD`) with `R = Fin 18`, `x0 r = x0E r pt0`, `rowOf x = ⟨labE 0 x.1, _⟩`;
* the row formula `Pmat pv (x0_r) y = pv (keyOf r (labE r y.1))` (`RowFacts`);
* the label bounds `labE r y.1 < ngE r` (`RowSem` for `r = 0`, `GroupSem` otherwise) and the
  fibre decomposition of the `y`-sum;
* `orbitConjPos` / `orbitConjZero`: every `y` is conjugate to the group representative
  `grepEI r (labE r y.1)`, so `fE(x0_r)⁻¹ fE y` is `Sg`-conjugate to `lprod 5 (keyWord r g)`
  (`keyWordLprod`) — hence the termwise `conjAvg` only depends on the label `g`;
* `cardFiber` (via `RowSem`/`GroupSem`) and `ClassSem`'s `multE (keyOf r g) = cntL r * sizeE r g`
  for the multiplicities.
-/

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section



namespace Work.PTCert

open Work.PTCert.OrbitKeys

private lemma conjAvg_add {G : Type} [Group G] (Sg : Finset G) (x y : MonoidAlgebra ℝ G) :
    conjAvg Sg (x + y) = conjAvg Sg x + conjAvg Sg y := by
  simp only [conjAvg, mul_add, add_mul, Finset.sum_add_distrib]

private lemma conjAvg_smul {G : Type} [Group G] (Sg : Finset G) (a : ℝ) (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (a • x) = a • conjAvg Sg x := by
  simp only [conjAvg]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [mul_smul_comm, smul_mul_assoc]

private lemma conjAvg_sum {G : Type} [Group G] {κ : Type} (Sg : Finset G) (s : Finset κ)
    (F : κ → MonoidAlgebra ℝ G) :
    conjAvg Sg (∑ i ∈ s, F i) = ∑ i ∈ s, conjAvg Sg (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conjAvg]
  | insert a t ha ih => rw [Finset.sum_insert ha, conjAvg_add, ih, Finset.sum_insert ha]

private lemma conjAvg_sum' {G : Type} [Group G] {κ : Type} [Fintype κ] (Sg : Finset G)
    (F : κ → MonoidAlgebra ℝ G) :
    conjAvg Sg (∑ i, F i) = ∑ i, conjAvg Sg (F i) := by
  simpa using conjAvg_sum Sg Finset.univ F

private lemma conjAvg_sum_EI (Sg : Finset G5) (s : Finset EI) (F : EI → MonoidAlgebra ℝ G5) :
    conjAvg Sg (∑ i ∈ s, F i) = ∑ i ∈ s, conjAvg Sg (F i) := conjAvg_sum Sg s F

private lemma conjAvg_sum_fin {n : ℕ} (Sg : Finset G5) (F : Fin n → MonoidAlgebra ℝ G5) :
    conjAvg Sg (∑ i : Fin n, F i) = ∑ i : Fin n, conjAvg Sg (F i) := conjAvg_sum' Sg F

private lemma conjAvg_conj {G : Type} [Group G] (Sg : Finset G) (hSg : IsFinSubgroup Sg) {s : G}
    (hs : s ∈ Sg) (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (MonoidAlgebra.of ℝ G s * x * MonoidAlgebra.of ℝ G s⁻¹) = conjAvg Sg x := by
  simp only [conjAvg]
  refine Finset.sum_nbij' (fun u => u * s) (fun v => v * s⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro u hu; exact hSg.2.1 u hu s hs
  · intro v hv; exact hSg.2.1 v hv s⁻¹ (hSg.2.2 s hs)
  · intro u _; simp [mul_assoc]
  · intro v _; simp [mul_assoc]
  · intro u _
    rw [mul_inv_rev, map_mul, map_mul]
    noncomm_ring

theorem orbitKeys (hOD : OrbitDecomp) (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure)
    (hRF : RowFacts) (hE : ESem) (hN : NSem) (hT : TabSem) (hR : RowSem) (hG : GroupSem) (hC : ClassSem) :
    OrbitKeys := by
  intro pv
  classical
  have hConj : ConjAction Sg fE actE := hA.2.2.1
  have hbijE : ∀ σ ∈ Sg, Function.Bijective (actE σ) := hA.2.2.2.2.2.1
  have hrowform := (hRF pv).1
  have hinvP := (hRF pv).2.1
  have horb := (hRF pv).2.2
  have hng0 : ngE 0 = 18 := hG.1
  have hgrep0 : ∀ g < 18, grepE 0 g = x0c g := hG.2.1
  have hGmain := hG.2.2
  have hx00 : x0c 0 = 0 := hR.1
  have hx0mem : ∀ r < 18, x0c r ∈ eAll := hR.2.1
  have hlab0lt : ∀ z ∈ eAll, labE 0 z < 18 := hR.2.2.2.2.1
  have hmult : ∀ r < 18, ∀ g < ngE r, multE (keyOf r g) = cntL.getD r 0 * sizeE r g := by
    have h := hC
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12⟩ := h
    exact h12
  have hSg : IsFinSubgroup Sg := (sigmaGroupFacts 5).1
  -- the label bound
  have hbound : ∀ (r : ℕ) (hr : r < 18) (y : EI), labE r y.1 < ngE r := by
    intro r hr y
    have hy : y.1 ∈ eAll := (mem_eS_iff y.1).mp y.2
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      rw [hng0]
      exact hlab0lt y.1 hy
    · exact ((hGmain r hr hpos).1 y.1 hy).1
  -- the orbit hypothesis for `hOD`
  have horbit : ∀ x : EI, ∃ σ ∈ Sg, actE σ (x0E (labE 0 x.1) pt0) = x := by
    intro x
    obtain ⟨σ, hσ, x', hx', hact⟩ := (horb x).2
    refine ⟨σ, hσ, ?_⟩
    have hxx0 : x' = x0E (labE 0 x.1) pt0 := by
      apply Subtype.ext
      show x'.1 = (x0E (labE 0 x.1) pt0).1
      rw [hx']
      exact (x0E_val hR (horb x).1).symm
    rw [← hxx0]; exact hact
  -- the row cardinalities
  have hcntR : ∀ r : Fin 18,
      ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ)
        = (cntL.getD r.1 0 : ℝ) := by
    intro r
    have hE1 : (Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r))
        = (Finset.univ.filter (fun y : EI => labE 0 y.1 = r.1)) := by
      refine Finset.filter_congr (fun x _ => ?_)
      constructor
      · intro h; exact congrArg Fin.val h
      · intro h; exact Fin.ext h
    rw [hE1, cardFiber hE hR hG (r := 0) (g := r.1) (by norm_num) (by rw [hng0]; exact r.2)]
    have hsz : sizeE 0 r.1 = cntL.getD r.1 0 := by simp [sizeE, sizesL]
    rw [hsz]
  -- reindexing of `conjAvg`
  have hconj_of : ∀ (σ : G5) (hσ : σ ∈ Sg) (L : G5),
      conjAvg Sg (MonoidAlgebra.of ℝ G5 (σ * L * σ⁻¹)) = conjAvg Sg (MonoidAlgebra.of ℝ G5 L) := by
    intro σ hσ L
    have h := conjAvg_conj Sg hSg hσ (MonoidAlgebra.of ℝ G5 L)
    rwa [← map_mul, ← map_mul] at h
  -- the conjugation of the row term
  have conjfact : ∀ (r : ℕ) (hr : r < 18) (y : EI),
      ∃ σ ∈ Sg, (fE (x0E r pt0))⁻¹ * fE y = σ * lprod 5 (keyWord r (labE r y.1)) * σ⁻¹ := by
    intro r hr y
    have hx0mem' : x0c r ∈ eS := mem_eS_of_mem _ (hx0mem r hr)
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      obtain ⟨σ, hσ, hconj⟩ := orbitConjZero hA hG hRF y
      refine ⟨σ, hσ, ?_⟩
      have hgmem : grepE 0 (labE 0 y.1) ∈ eS :=
        grepE_mem_zero hG hR (hbound 0 (by norm_num) y)
      have hkey : fE (grepEI 0 (labE 0 y.1)) = lprod 5 (keyWord 0 (labE 0 y.1)) := by
        rw [fE_grepEI hgmem, keyWordLprod hE hx0mem', hx00, Work.PTCert.eltC_zero, inv_one, one_mul]
      calc (fE (x0E 0 pt0))⁻¹ * fE y
          = fE y := by rw [fE_x0E_zero hR, inv_one, one_mul]
        _ = σ * fE (grepEI 0 (labE 0 y.1)) * σ⁻¹ := hconj
        _ = σ * lprod 5 (keyWord 0 (labE 0 y.1)) * σ⁻¹ := by rw [hkey]
    · obtain ⟨σ, hσ, hact1, hact2⟩ := orbitConjPos hCF hA hE hR hG hpos hr y
      refine ⟨σ, hσ, ?_⟩
      have hgmem : grepE r (labE r y.1) ∈ eS := grepE_mem_pos hG hr hpos (hbound r hr y)
      have hkey : lprod 5 (keyWord r (labE r y.1)) =
          (fE (x0E r pt0))⁻¹ * fE (grepEI r (labE r y.1)) := by
        rw [keyWordLprod hE hx0mem', ← fE_x0E hR hr, ← fE_grepEI hgmem]
      have hfy : fE y = σ * fE (grepEI r (labE r y.1)) * σ⁻¹ := by
        have h := hConj.2 σ hσ (grepEI r (labE r y.1))
        rwa [hact1] at h
      have hfx : fE (x0E r pt0) = σ * fE (x0E r pt0) * σ⁻¹ := by
        have h := hConj.2 σ hσ (x0E r pt0)
        rwa [hact2] at h
      calc (fE (x0E r pt0))⁻¹ * fE y
          = (σ * fE (x0E r pt0) * σ⁻¹)⁻¹ * (σ * fE (grepEI r (labE r y.1)) * σ⁻¹) := by
            conv_lhs => rw [hfy, hfx]
        _ = σ * ((fE (x0E r pt0))⁻¹ * fE (grepEI r (labE r y.1))) * σ⁻¹ := by group
        _ = σ * lprod 5 (keyWord r (labE r y.1)) * σ⁻¹ := by rw [← hkey]
  -- the row lemma
  have rowlemma : ∀ r : ℕ, r < 18 →
      conjAvg Sg (∑ y : EI, ((pv (keyOf r (labE r y.1)) : ℝ)) •
        MonoidAlgebra.of ℝ G5 ((fE (x0E r pt0))⁻¹ * fE y))
      = ∑ g ∈ Finset.range (ngE r), ((sizeE r g : ℝ) * (pv (keyOf r g) : ℝ)) •
          conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))) := by
    intro r hr
    -- step 1: split the sum by the value of the label
    have hfib : (∑ y : EI, ((pv (keyOf r (labE r y.1)) : ℝ)) •
          MonoidAlgebra.of ℝ G5 ((fE (x0E r pt0))⁻¹ * fE y))
        = ∑ j : Fin (ngE r), ∑ y ∈ Finset.univ.filter
            (fun y : EI => (⟨labE r y.1, hbound r hr y⟩ : Fin (ngE r)) = j),
          ((pv (keyOf r j.1) : ℝ)) •
            MonoidAlgebra.of ℝ G5 ((fE (x0E r pt0))⁻¹ * fE y) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun y : EI => (⟨labE r y.1, hbound r hr y⟩ : Fin (ngE r)))
        (fun y => ((pv (keyOf r (labE r y.1)) : ℝ)) •
          MonoidAlgebra.of ℝ G5 ((fE (x0E r pt0))⁻¹ * fE y))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hjy : labE r y.1 = j.1 := congrArg Fin.val (Finset.mem_filter.mp hy).2
      rw [hjy]
    rw [hfib]
    -- step 3: `conjAvg` is linear, and each term is conjugate to the key
    rw [conjAvg_sum_fin]
    have hterm : ∀ j : Fin (ngE r),
        conjAvg Sg (∑ y ∈ Finset.univ.filter
            (fun y : EI => (⟨labE r y.1, hbound r hr y⟩ : Fin (ngE r)) = j),
            ((pv (keyOf r j.1) : ℝ)) •
              MonoidAlgebra.of ℝ G5 ((fE (x0E r pt0))⁻¹ * fE y))
          = ((sizeE r j.1 : ℝ) * (pv (keyOf r j.1) : ℝ)) •
              conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r j.1))) := by
      intro j
      rw [conjAvg_sum_EI]
      have hinner : ∀ y ∈ Finset.univ.filter
          (fun y : EI => (⟨labE r y.1, hbound r hr y⟩ : Fin (ngE r)) = j),
          conjAvg Sg (((pv (keyOf r j.1) : ℝ)) •
              MonoidAlgebra.of ℝ G5 ((fE (x0E r pt0))⁻¹ * fE y))
            = ((pv (keyOf r j.1) : ℝ)) •
              conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r j.1))) := by
        intro y hy
        have hbase : conjAvg Sg (MonoidAlgebra.of ℝ G5 ((fE (x0E r pt0))⁻¹ * fE y))
            = conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r j.1))) := by
          have hjy : labE r y.1 = j.1 := congrArg Fin.val (Finset.mem_filter.mp hy).2
          obtain ⟨σ, hσ, hconj⟩ := conjfact r hr y
          rw [hconj, hjy]
          exact hconj_of σ hσ (lprod 5 (keyWord r j.1))
        rw [conjAvg_smul, hbase]
      have hfilt : (Finset.univ.filter
            (fun y : EI => (⟨labE r y.1, hbound r hr y⟩ : Fin (ngE r)) = j))
          = (Finset.univ.filter (fun y : EI => labE r y.1 = j.1)) := by
        refine Finset.filter_congr (fun y _ => ?_)
        constructor
        · intro h; exact congrArg Fin.val h
        · intro h; exact Fin.ext h
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hfilt,
        cardFiber hE hR hG hr j.2]
    exact (Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ => hterm j)).trans
      (Fin.sum_univ_eq_sum_range (fun g => ((sizeE r g : ℝ) * (pv (keyOf r g) : ℝ)) •
        conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g)))) (ngE r))
  -- assembly
  have hZ : ∀ r : Fin 18,
      (∑ y : EI, Pmat pv (x0E r.1 pt0) y • MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y))
      = (∑ y : EI, ((pv (keyOf r.1 (labE r.1 y.1)) : ℝ)) •
          MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)) := by
    intro r
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hrowform r.1 r.2 (x0E r.1 pt0) y (x0E_val hR r.2)]
  have hOD' : conjAvg Sg (gramForm fE (Pmat pv)) = conjAvg Sg (∑ r : Fin 18,
      ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
        ∑ y : EI, Pmat pv (x0E r.1 pt0) y • MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)) :=
    hOD G5 Sg hSg fE actE hConj hbijE (Pmat pv) hinvP (fun r : Fin 18 => x0E r.1 pt0)
      (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18)) horbit
  have step2 : conjAvg Sg (∑ r : Fin 18,
        ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          (∑ y : EI, Pmat pv (x0E r.1 pt0) y • MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)))
      = ∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          conjAvg Sg (∑ y : EI, ((pv (keyOf r.1 (labE r.1 y.1)) : ℝ)) •
            MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)) := by
    have h1 : (∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          (∑ y : EI, Pmat pv (x0E r.1 pt0) y • MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)))
        = ∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          (∑ y : EI, ((pv (keyOf r.1 (labE r.1 y.1)) : ℝ)) •
            MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)) :=
      Finset.sum_congr rfl (fun r _ => by rw [hZ r])
    rw [h1, conjAvg_sum']
    exact Finset.sum_congr rfl (fun r _ => conjAvg_smul Sg _ _)
  have step3 : (∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          conjAvg Sg (∑ y : EI, ((pv (keyOf r.1 (labE r.1 y.1)) : ℝ)) •
            MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)))
      = ∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          (∑ g ∈ Finset.range (ngE r.1), ((sizeE r.1 g : ℝ) * (pv (keyOf r.1 g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r.1 g)))) :=
    Finset.sum_congr rfl (fun r _ => by rw [rowlemma r.1 r.2])
  have step4 : (∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          (∑ g ∈ Finset.range (ngE r.1), ((sizeE r.1 g : ℝ) * (pv (keyOf r.1 g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r.1 g)))))
      = ∑ r : Fin 18, ∑ g ∈ Finset.range (ngE r.1),
          ((multE (keyOf r.1 g) : ℝ) * (pv (keyOf r.1 g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r.1 g))) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    rw [smul_smul]
    have hmul : (multE (keyOf r.1 g) : ℝ) = (cntL.getD r.1 0 : ℝ) * (sizeE r.1 g : ℝ) := by
      rw [hmult r.1 r.2 g (Finset.mem_range.mp hg), Nat.cast_mul]
    rw [hcntR r, hmul, mul_assoc]
  have step5 : (∑ r : Fin 18, ∑ g ∈ Finset.range (ngE r.1),
          ((multE (keyOf r.1 g) : ℝ) * (pv (keyOf r.1 g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r.1 g))))
      = ∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))) := by
    rw [Fin.sum_univ_eq_sum_range (fun r => ∑ g ∈ Finset.range (ngE r),
      ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
        conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g)))) 18]
  have step6 : (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))))
      = conjAvg Sg (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
            MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))) := by
    have h : (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))))
        = (∑ r ∈ Finset.range 18, conjAvg Sg (∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
            MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g)))) := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [conjAvg_sum Sg]
      exact Finset.sum_congr rfl (fun g _ => (conjAvg_smul Sg _ _).symm)
    rw [h, ← conjAvg_sum]
  calc conjAvg Sg (gramForm fE (Pmat pv))
      = conjAvg Sg (∑ r : Fin 18,
          ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
            ∑ y : EI, Pmat pv (x0E r.1 pt0) y • MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)) := hOD'
    _ = ∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          conjAvg Sg (∑ y : EI, ((pv (keyOf r.1 (labE r.1 y.1)) : ℝ)) •
            MonoidAlgebra.of ℝ G5 ((fE (x0E r.1 pt0))⁻¹ * fE y)) := step2
    _ = ∑ r : Fin 18, ((Finset.univ.filter (fun x : EI => (⟨labE 0 x.1, (horb x).1⟩ : Fin 18) = r)).card : ℝ) •
          (∑ g ∈ Finset.range (ngE r.1), ((sizeE r.1 g : ℝ) * (pv (keyOf r.1 g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r.1 g)))) := step3
    _ = ∑ r : Fin 18, ∑ g ∈ Finset.range (ngE r.1),
          ((multE (keyOf r.1 g) : ℝ) * (pv (keyOf r.1 g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r.1 g))) := step4
    _ = ∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
            conjAvg Sg (MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))) := step5
    _ = conjAvg Sg (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
            MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))) := step6

end Work.PTCert

