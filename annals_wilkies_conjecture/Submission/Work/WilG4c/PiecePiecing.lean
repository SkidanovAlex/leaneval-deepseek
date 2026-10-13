import Mathlib
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG0.API

/-
  WilG4c / PiecePiecing: BNZ's "piecewise gluing" of chart families.

  Given a finite cover of the parameter space by `Ω`-bounded sets `P σ`, and chart families
  valid (and `ε`-covering) only on the pieces `Λ ∩ P σ`, produce a single chart family valid
  and `ε`-covering on all of `Λ`, with at most `|ι| · M` charts.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## `Ω`-calculus for the clamped (piecewise) family

The statement of `PiecePiecing` clamps every chart of the `σ`-th piece to the constant `1/2`
outside `P σ`.  To control the graphs of the clamped charts we need the `Ω`-membership of the
clamped family, i.e. the "cut a family down to a definable parameter set" computation. -/

/-- Reading membership in `famGraph h` in coordinates. -/
theorem mem_famGraph_coords_aux {p m : ℕ} (h : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (z : Fin (p + m + 1) → ℝ) :
    z ∈ famGraph h ↔
      z (Fin.last (p + m)) = h (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
        (fun j : Fin m => (Fin.init z) (Fin.natAdd p j)) := by
  simp only [famGraph, graphOf, Set.mem_ofPred_eq]

/-- The hyperplane `{z | z (last) = c}` in `ℝ^{N+1}` is `Ω (N+1) 1`-bounded. -/
theorem lastCoord_eq_mem_aux (S : SOMin) (N : ℕ) (c : ℝ) :
    {z : Fin (N + 1) → ℝ | z (Fin.last N) = c} ∈ S.Ω (N + 1) 1 (N + 1) := by
  have h := S.hyp (N + 1)
    (MvPolynomial.X (Fin.last N) - MvPolynomial.C c : MvPolynomial (Fin (N + 1)) ℝ)
  have hset : {x : Fin (N + 1) → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (Fin.last N) - MvPolynomial.C c : MvPolynomial (Fin (N + 1)) ℝ) = 0}
      = {z : Fin (N + 1) → ℝ | z (Fin.last N) = c} := by
    ext z
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, sub_eq_zero]
  rw [hset] at h
  refine Work.WilG0.Omega_mono_D (S := S) ?_ h
  exact le_trans (MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X (Fin.last N)) c)
    (le_of_eq (MvPolynomial.totalDegree_X (Fin.last N)))

/-- The pullback of a parameter set to `ℝ^{p+m}`: the points whose first `p` coordinates lie
in `Λ`. -/
def clampParSet (p m : ℕ) (Λ : Set (Fin p → ℝ)) : Set (Fin (p + m) → ℝ) :=
  {w | (fun i : Fin p => w (Fin.castAdd m i)) ∈ Λ}

@[simp] theorem mem_clampParSet {p m : ℕ} {Λ : Set (Fin p → ℝ)} {w : Fin (p + m) → ℝ} :
    w ∈ clampParSet p m Λ ↔ (fun i : Fin p => w (Fin.castAdd m i)) ∈ Λ :=
  Iff.rfl

/-- `clampParSet` preserves `Ω`-membership: it is an iterated `prod_right`, so the format grows
by `m` and the degree does not change. -/
theorem clampParSet_mem (S : SOMin) {p m F D : ℕ} {Λ : Set (Fin p → ℝ)}
    (hΛ : Λ ∈ S.Ω F D p) :
    {z : Fin (p + m) → ℝ | (fun i : Fin p => z (Fin.castAdd m i)) ∈ Λ}
      ∈ S.Ω (F + m) D (p + m) := by
  induction m with
  | zero =>
      have hset : {z : Fin (p + 0) → ℝ | (fun i : Fin p => z (Fin.castAdd 0 i)) ∈ Λ} = Λ := by
        ext z
        show ((fun i : Fin p => z (Fin.castAdd 0 i)) ∈ Λ) ↔ (z ∈ Λ)
        rw [show (fun i : Fin p => z (Fin.castAdd 0 i)) = z from funext (fun i => rfl)]
      rw [hset]; simpa using hΛ
  | succ m ih =>
      have hstep : {z : Fin (p + (m + 1)) → ℝ |
          Fin.init z ∈ {z : Fin (p + m) → ℝ | (fun i : Fin p => z (Fin.castAdd m i)) ∈ Λ}} ∈
          S.Ω (F + (m + 1)) D (p + (m + 1)) := S.prod_right ih
      have hset : {z : Fin (p + (m + 1)) → ℝ |
            (fun i : Fin p => z (Fin.castAdd (m + 1) i)) ∈ Λ}
          = {z : Fin (p + (m + 1)) → ℝ |
              Fin.init z ∈ {z : Fin (p + m) → ℝ |
                (fun i : Fin p => z (Fin.castAdd m i)) ∈ Λ}} := by
        ext z
        show ((fun i : Fin p => z (Fin.castAdd (m + 1) i)) ∈ Λ) ↔
          ((fun i : Fin p => (Fin.init z) (Fin.castAdd m i)) ∈ Λ)
        refine iff_of_eq (congrArg (fun w : Fin p → ℝ => w ∈ Λ) ?_)
        funext i
        simp only [Fin.init]
        rw [Fin.castSucc_castAdd]
      rw [hset]
      exact hstep

/-- The clamped graph identity: if `g` agrees with `f` on the parameter set `Λ` and equals the
constant `c` outside it, then the graph of `g` is the graph of `f` restricted to `Λ`, together
with the value hyperplane `u = c` over the complement of `Λ`. -/
theorem famGraph_ite_eq_aux {p m : ℕ} (Λ : Set (Fin p → ℝ)) (c : ℝ)
    (f g : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (hfg : ∀ l t, l ∈ Λ → g l t = f l t)
    (hgc : ∀ l t, l ∉ Λ → g l t = c) :
    famGraph g =
      (famGraph f ∩ {z : Fin (p + m + 1) → ℝ | Fin.init z ∈ clampParSet p m Λ}) ∪
        (({z : Fin (p + m + 1) → ℝ | Fin.init z ∈ clampParSet p m Λ})ᶜ ∩
          {z : Fin (p + m + 1) → ℝ | z (Fin.last (p + m)) = c}) := by
  ext z
  rw [mem_famGraph_coords_aux g z]
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
    mem_famGraph_coords_aux f z, mem_clampParSet]
  by_cases hl : (fun i : Fin p => (Fin.init z) (Fin.castAdd m i)) ∈ Λ
  · have key : g (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
        (fun j : Fin m => (Fin.init z) (Fin.natAdd p j))
        = f (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
          (fun j : Fin m => (Fin.init z) (Fin.natAdd p j)) := hfg _ _ hl
    rw [key]
    simp [hl]
  · have key : g (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
        (fun j : Fin m => (Fin.init z) (Fin.natAdd p j)) = c := hgc _ _ hl
    rw [key]
    simp [hl]

/-- **The clamped family member has an `Ω`-bounded graph.**  If `Λ` and the graph of `F i` are
`Ω`-bounded then the member which agrees with `F i` on `Λ` and is the constant `c` outside `Λ`
has an `Ω`-bounded graph.  The format and degree grow additively. -/
theorem clampedFamGraph_mem (S : SOMin) {p n k : ℕ} (Λ : Set (Fin p → ℝ)) (c : ℝ)
    (F G : Family k p (n + 1)) (i : Fin k) (aΛ dP F0 D : ℕ)
    (hΛ : Λ ∈ S.Ω aΛ dP p)
    (hF : famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1))
    (hG : ∀ l t, l ∈ Λ → G i l t = F i l t)
    (hGc : ∀ l t, l ∉ Λ → G i l t = c) :
    famGraph (G i) ∈
      S.Ω (F0 + aΛ + 5 * (p + (n + 1) + 1) + 5 * p + 20) (2 * D + 2 * dP + 20)
        (p + (n + 1) + 1) := by
  rw [famGraph_ite_eq_aux (m := n + 1) Λ c (F i) (G i) hG hGc]
  -- the pieces
  have hA : clampParSet p (n + 1) Λ ∈ S.Ω (aΛ + (n + 1)) dP (p + (n + 1)) :=
    clampParSet_mem S hΛ
  have hA1 : {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ clampParSet p (n + 1) Λ} ∈
      S.Ω (aΛ + (n + 1) + 1) dP (p + (n + 1) + 1) := S.prod_right hA
  have hAc : ({z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ clampParSet p (n + 1) Λ})ᶜ ∈
      S.Ω (aΛ + (n + 1) + 2) dP (p + (n + 1) + 1) := S.compl hA1
  have hH : {z : Fin (p + (n + 1) + 1) → ℝ | z (Fin.last (p + (n + 1))) = c} ∈
      S.Ω (F0 + (aΛ + (n + 1) + 2) + (p + (n + 1) + 1)) 1 (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (lastCoord_eq_mem_aux S (p + (n + 1)) c)
  -- a common format
  have hF' : famGraph (F i) ∈
      S.Ω (F0 + (aΛ + (n + 1) + 2) + (p + (n + 1) + 1)) D (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_F (by omega) hF
  have hA1' : {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ clampParSet p (n + 1) Λ} ∈
      S.Ω (F0 + (aΛ + (n + 1) + 2) + (p + (n + 1) + 1)) dP (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_F (by omega) hA1
  have hAc' : ({z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ clampParSet p (n + 1) Λ})ᶜ ∈
      S.Ω (F0 + (aΛ + (n + 1) + 2) + (p + (n + 1) + 1)) dP (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_F (by omega) hAc
  have hI1 := Work.WilG0.Omega_inter2 hF' hA1'
  have hI2 := Work.WilG0.Omega_inter2 hAc' hH
  have hU := Work.WilG0.Omega_union2 hI1 hI2
  exact Work.WilG0.Omega_mono_FD (by omega) (by omega) hU

/-! ## `ChartsOK` for clamped charts -/

/-- Generalized `ChartsOK` extension: given charts `Φ` that are `ChartsOK` on `Λ ∩ Λ'`, and a
modification `mod` that is the identity on `Λ'` and the constant `c` outside `Λ'`, whose
components still have `Ω`-bounded graphs, the modified charts are `ChartsOK` on all of `Λ`;
their number does not increase. -/
theorem ChartsOK_clamp_aux {S : SOMin} {p n k a Dg r : ℕ}
    {Λ Λ' : Set (Fin p → ℝ)} {F : Family k p n}
    {Φ : Finset (ChartTuple p n)} {c : Fin n → ℝ}
    (hc : c ∈ openCube n) (hval : ValuesIn01 Λ F)
    (mod : ChartTuple p n → ChartTuple p n)
    (hmod : ∀ φ j l, l ∈ Λ' → ∀ t : Fin n → ℝ, mod φ j l t = φ j l t)
    (hmodc : ∀ φ j l, l ∉ Λ' → ∀ t : Fin n → ℝ, mod φ j l t = c j)
    (hΩ : ∀ φ ∈ Φ, ∀ j : Fin n, famGraph ((mod φ) j) ∈ S.Ω a Dg (p + n + 1))
    (h : ∀ φ ∈ Φ, ∀ l, l ∈ Λ ∩ Λ' →
      (∀ t ∈ openCube n, (fun j => φ j l t) ∈ openCube n) ∧
      ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t)) (openCube n) ∧
        ∀ m, m ≤ r → ∀ t ∈ openCube n,
          ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1) :
    ∃ Φ' : Finset (ChartTuple p n),
      (∀ φ ∈ Φ, mod φ ∈ Φ') ∧ Φ'.card ≤ Φ.card ∧ ChartsOK S a Dg r Λ F Φ' := by
  classical
  refine ⟨Φ.image mod, ?_, Finset.card_image_le, ?_⟩
  · intro φ hφ
    exact Finset.mem_image_of_mem mod hφ
  · rw [ChartsOK]
    intro φ' hφ'
    rw [Finset.mem_image] at hφ'
    obtain ⟨φ, hφ, rfl⟩ := hφ'
    refine ⟨fun j => hΩ φ hφ j, ?_⟩
    intro l hl
    by_cases hl' : l ∈ Λ'
    · obtain ⟨hcube, hrest⟩ := h φ hφ l ⟨hl, hl'⟩
      have hpt : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = (fun j => φ j l t) :=
        fun t => funext (fun j => hmod φ j l hl' t)
      have hfun : ∀ i, (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
          = (fun t : Fin n → ℝ => F i l (fun j => φ j l t)) :=
        fun i => funext (fun t => by congr 1; funext j; exact hmod φ j l hl' t)
      refine ⟨fun t ht => by rw [hpt t]; exact hcube t ht, ?_⟩
      intro i
      constructor
      · rw [hfun i]; exact (hrest i).1
      · intro m hm t ht
        rw [hfun i]; exact (hrest i).2 m hm t ht
    · have hconst : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = c :=
        fun t => funext (fun j => hmodc φ j l hl' t)
      refine ⟨fun t ht => by rw [hconst t]; exact hc, ?_⟩
      intro i
      have hfun : (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
          = (fun _ : Fin n → ℝ => F i l c) :=
        funext (fun t => by rw [hconst t])
      constructor
      · rw [hfun]; exact contDiffOn_const
      · intro m hm t ht
        rw [hfun]
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hval i l hl c hc).1]
          exact le_of_lt (hval i l hl c hc).2
        · rw [iteratedFDeriv_const_of_ne (ne_of_gt hpos) (F i l c)]
          simp

end Work.WilkG4c

/-! ## Piecing the per-piece chart families together -/

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

theorem PiecePiecing (S : WilkiesDesign.SOMin) (p n k : ℕ) :
    ∃ (a' : ℕ) (c' : ℕ), ∀ (D r : ℕ) (ι : Type) [Fintype ι]
      (P : ι → Set (Fin p → ℝ)) (aΛ : ℕ) (dΛ : MvPolynomial (Fin 2) ℕ)
      (hP : ∀ σ, P σ ∈ S.Ω aΛ (MvPolynomial.eval ![D, r] dΛ) p)
      (hcovP : ∀ l : Fin p → ℝ, ∃ σ, l ∈ P σ)
      (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
      (hval : Work.WilkG4c.ValuesIn01 Λ F)
      (ε : ℝ) (a Dg : ℕ) (Φ : ι → Finset (Work.WilkG4c.ChartTuple p (n + 1))) (M : ℝ)
      (hOK : ∀ σ, Work.WilkG4c.ChartsOK S a Dg r (Λ ∩ P σ) F (Φ σ))
      (hcv : ∀ σ, Work.WilkG4c.Covers (Λ ∩ P σ) F (Φ σ) ε)
      (hcard : ∀ σ, ((Φ σ).card : ℝ) ≤ M),
      ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
        ((Φ'.card : ℝ) ≤ (Fintype.card ι : ℝ) * M) ∧
        Work.WilkG4c.ChartsOK S (aΛ + a + a')
          (4 * (MvPolynomial.eval ![D, r] dΛ) + 4 * Dg + c') r Λ F Φ' ∧
        Work.WilkG4c.Covers Λ F Φ' ε := by
  classical
  refine ⟨5 * (p + (n + 1) + 1) + 5 * p + 20, 20, ?_⟩
  intro D r ι _ P aΛ dΛ hP hcovP Λ F hval ε a Dg Φ M hOK hcv hcard
  -- clamp each chart to the constant `1/2` outside the parameter set `P σ`
  let sel : ι → Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1) :=
    fun σ φ j l t => if l ∈ P σ then φ j l t else (1 / 2 : ℝ)
  have hsel : ∀ (σ : ι) (φ : Work.WilkG4c.ChartTuple p (n + 1)) (j : Fin (n + 1))
      (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ),
      sel σ φ j l t = if l ∈ P σ then φ j l t else (1 / 2 : ℝ) := fun _ _ _ _ _ => rfl
  have hc : (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) ∈ WilkiesDesign.openCube (n + 1) := by
    intro j; norm_num
  -- the clamped charts still have `Ω`-bounded graphs
  have hΩ : ∀ (σ : ι) (φ : Work.WilkG4c.ChartTuple p (n + 1)), φ ∈ Φ σ → ∀ j : Fin (n + 1),
      famGraph ((sel σ φ) j) ∈
        S.Ω (aΛ + a + (5 * (p + (n + 1) + 1) + 5 * p + 20))
          (4 * (MvPolynomial.eval ![D, r] dΛ) + 4 * Dg + 20) (p + (n + 1) + 1) := by
    intro σ φ hφ j
    have hφmem : famGraph (φ j) ∈ S.Ω a Dg (p + (n + 1) + 1) := (hOK σ φ hφ).1 j
    have hraw := clampedFamGraph_mem (S := S) (p := p) (n := n) (k := 1) (P σ) (1 / 2 : ℝ)
      (fun _ : Fin 1 => φ j) (fun _ : Fin 1 => (sel σ φ) j) 0
      aΛ (MvPolynomial.eval ![D, r] dΛ) a Dg (hP σ) hφmem
      (fun l t hl => by simp only [hsel, if_pos hl])
      (fun l t hl => by simp only [hsel, if_neg hl])
    exact Work.WilG0.Omega_mono_FD (by omega) (by omega) hraw
  -- the clamped charts are `ChartsOK` on all of `Λ`
  have hExists : ∀ σ : ι, ∃ Ψ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
      (∀ φ ∈ Φ σ, sel σ φ ∈ Ψ) ∧ Ψ.card ≤ (Φ σ).card ∧
      ChartsOK S (aΛ + a + (5 * (p + (n + 1) + 1) + 5 * p + 20))
        (4 * (MvPolynomial.eval ![D, r] dΛ) + 4 * Dg + 20) r Λ F Ψ := by
    intro σ
    exact ChartsOK_clamp_aux (S := S) (F := F) (Φ := Φ σ) (Λ := Λ) (Λ' := P σ)
      (c := fun _ : Fin (n + 1) => (1 / 2 : ℝ)) hc hval (sel σ)
      (fun φ j l hl t => by simp only [hsel, if_pos hl])
      (fun φ j l hl t => by simp only [hsel, if_neg hl])
      (fun φ hφ j => hΩ σ φ hφ j)
      (fun φ hφ l hl => (hOK σ φ hφ).2 l hl)
  choose Ψ hΨ using hExists
  refine ⟨Finset.univ.biUnion Ψ, ?_, ?_, ?_⟩
  · -- cardinality
    calc ((Finset.univ.biUnion Ψ).card : ℝ)
        ≤ ((Finset.univ.sum (fun σ : ι => (Ψ σ).card) : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := Ψ))
      _ = Finset.univ.sum (fun σ : ι => ((Ψ σ).card : ℝ)) := by rw [Nat.cast_sum]
      _ ≤ Finset.univ.sum (fun _ : ι => M) :=
          Finset.sum_le_sum (fun σ _ => le_trans (by exact_mod_cast (hΨ σ).2.1) (hcard σ))
      _ = (Fintype.card ι : ℝ) * M := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · -- `ChartsOK` is a per-chart condition
    rw [ChartsOK]
    intro φ hφ
    rw [Finset.mem_biUnion] at hφ
    obtain ⟨σ, _, hφσ⟩ := hφ
    exact (hΨ σ).2.2 φ hφσ
  · -- covering
    rw [Covers]
    intro l hl x hx
    obtain ⟨σ, hσ⟩ := hcovP l
    obtain ⟨φ, hφ, t, ht, hlt⟩ := hcv σ l ⟨hl, hσ⟩ x hx
    refine ⟨sel σ φ, ?_, t, ht, ?_⟩
    · rw [Finset.mem_biUnion]
      exact ⟨σ, Finset.mem_univ σ, (hΨ σ).1 φ hφ⟩
    · intro i
      have hpt : (fun j : Fin (n + 1) => sel σ φ j l t) = (fun j : Fin (n + 1) => φ j l t) :=
        funext (fun j => by simp only [hsel, if_pos hσ])
      rw [hpt]
      exact hlt i

end Work.WilG4c

/- The same lemma under the namespace spelling of the original request. -/
namespace Work.WilkG4c

theorem PiecePiecing (S : WilkiesDesign.SOMin) (p n k : ℕ) :
    ∃ (a' : ℕ) (c' : ℕ), ∀ (D r : ℕ) (ι : Type) [Fintype ι]
      (P : ι → Set (Fin p → ℝ)) (aΛ : ℕ) (dΛ : MvPolynomial (Fin 2) ℕ)
      (hP : ∀ σ, P σ ∈ S.Ω aΛ (MvPolynomial.eval ![D, r] dΛ) p)
      (hcovP : ∀ l : Fin p → ℝ, ∃ σ, l ∈ P σ)
      (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
      (hval : Work.WilkG4c.ValuesIn01 Λ F)
      (ε : ℝ) (a Dg : ℕ) (Φ : ι → Finset (Work.WilkG4c.ChartTuple p (n + 1))) (M : ℝ)
      (hOK : ∀ σ, Work.WilkG4c.ChartsOK S a Dg r (Λ ∩ P σ) F (Φ σ))
      (hcv : ∀ σ, Work.WilkG4c.Covers (Λ ∩ P σ) F (Φ σ) ε)
      (hcard : ∀ σ, ((Φ σ).card : ℝ) ≤ M),
      ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
        ((Φ'.card : ℝ) ≤ (Fintype.card ι : ℝ) * M) ∧
        Work.WilkG4c.ChartsOK S (aΛ + a + a')
          (4 * (MvPolynomial.eval ![D, r] dΛ) + 4 * Dg + c') r Λ F Φ' ∧
        Work.WilkG4c.Covers Λ F Φ' ε :=
  _root_.Work.WilG4c.PiecePiecing S p n k

end Work.WilkG4c
