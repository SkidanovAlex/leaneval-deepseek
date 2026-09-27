import Mathlib
import Submission.Work.EQ.UnivCover.CountableSetup
import Submission.Work.EQ.UnivCover.UC_segPt_spec
import Submission.Work.EQ.UnivCover.chainPt_invariant
import Submission.Work.EQ.UnivCover.countable_zerothHomotopy

set_option autoImplicit false
open _root_.Topology
open scoped Topology unitInterval
open Classical

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X]

/-! ## Endpoints of the initial-segment map -/

/-- Extensionality of `UC` up to the endpoint cast of the class. -/
theorem UC.ext_cast {x₀ : X} : ∀ {e₁ e₂ : UC x₀} (h : e₁.pt = e₂.pt),
    e₁.cls.cast rfl h.symm = e₂.cls → e₁ = e₂ := by
  rintro ⟨p₁, c₁⟩ ⟨p₂, c₂⟩ h hc
  rw [UC.mk.injEq]
  exact ⟨h, (Path.Homotopic.Quotient.cast_heq rfl h.symm).symm.trans (heq_of_eq hc)⟩

theorem ucSegPt_zero {x₀ x : X} (γ : Path x₀ x) : UC.segPt γ 0 = UC.base x₀ := by
  refine UC.ext_cast γ.source ?_
  change (Path.Homotopic.Quotient.mk (segTo γ 0)).cast rfl γ.source.symm
    = Path.Homotopic.Quotient.refl x₀
  have hpath : (segTo γ 0).cast rfl γ.source.symm = Path.refl x₀ := by
    ext s
    change γ (s * (0 : unitInterval)) = x₀
    rw [show s * (0 : unitInterval) = 0 from Subtype.ext (by simp)]
    exact γ.source
  rw [← Path.Homotopic.Quotient.mk_cast, hpath, Path.Homotopic.Quotient.mk_refl]

theorem ucSegPt_one {x₀ x : X} (γ : Path x₀ x) :
    UC.segPt γ 1 = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) := by
  refine UC.ext_cast γ.target ?_
  change (Path.Homotopic.Quotient.mk (segTo γ 1)).cast rfl γ.target.symm
    = Path.Homotopic.Quotient.mk γ
  have hpath : (segTo γ 1).cast rfl γ.target.symm = γ := by
    ext s
    change γ (s * (1 : unitInterval)) = γ s
    rw [show s * (1 : unitInterval) = s from Subtype.ext (by simp)]
  rw [← Path.Homotopic.Quotient.mk_cast, hpath]

/-! ## The key step: the initial-segment point is stable under appending a disc-like leg -/

theorem step_segPt {U : ℕ → Set X} {hU : DiscCover U} {x₀ x : X} (γ : Path x₀ x)
    {n : ℕ} {s t : I} (hst : s ≤ t) (hn : ∀ u ∈ Set.Icc s t, γ u ∈ U n) :
    step U hU (UC.segPt γ s) n (γ t) = UC.segPt γ t := by
  have hX : (UC.segPt γ s).pt ∈ U n := hn s ⟨le_refl s, hst⟩
  have ht : γ t ∈ U n := hn t ⟨hst, le_refl t⟩
  rw [step_of_mem ⟨hX, ht⟩]
  have h1 : sectOf (U n) (hU.1 n) (UC.segPt γ s) hX (γ t) ht ∈ UC.sheet (UC.segPt γ s) (U n) :=
    sectOf_mem (U n) (hU.1 n) (UC.segPt γ s) hX (γ t) ht
  have h2 : UC.segPt γ t ∈ UC.sheet (UC.segPt γ s) (U n) := by
    refine ucSegPt_mem_sheet γ s t fun u hu => ?_
    rw [Set.uIcc_of_le hst] at hu
    exact hn u hu
  exact (UC_sheet_unique (hU.1 n)).1 h1 h2 rfl

/-! ## The chain of a subdivision reaches the initial-segment point -/

theorem chainPt_ofFn_segPt {U : ℕ → Set X} {hU : DiscCover U} {x₀ x : X} (γ : Path x₀ x) :
    ∀ (K : ℕ) (t : ℕ → I) (n : ℕ → ℕ), Monotone t →
      (∀ i u, u ∈ Set.Icc (t i) (t (i + 1)) → γ u ∈ U (n i)) →
      chainPt U hU (List.ofFn (fun i : Fin K => (n i.1, γ (t (i.1 + 1)))))
        (UC.segPt γ (t 0)) = UC.segPt γ (t K) := by
  intro K
  induction K with
  | zero =>
      intro t n ht hn
      rw [List.ofFn_zero, chainPt_nil]
  | succ K ih =>
      intro t n ht hn
      rw [List.ofFn_succ]
      show chainPt U hU (List.ofFn (fun i : Fin K => (n ((i.succ : Fin (K+1)) : ℕ),
              γ (t (((i.succ : Fin (K+1)) : ℕ) + 1)))))
            (step U hU (UC.segPt γ (t 0)) (n 0) (γ (t 1))) = UC.segPt γ (t (K + 1))
      rw [step_segPt γ (ht (Nat.zero_le 1)) (fun u hu => hn 0 u hu)]
      have hcongr : (fun i : Fin K => (n ((i.succ : Fin (K + 1)) : ℕ),
            γ (t (((i.succ : Fin (K + 1)) : ℕ) + 1))))
          = fun i : Fin K => ((fun j => n (j + 1)) i.1, γ ((fun j => t (j + 1)) (i.1 + 1))) := by
        funext i
        rw [Fin.val_succ]
      rw [hcongr]
      exact ih (fun j => t (j + 1)) (fun j => n (j + 1))
        (fun a b hab => ht (Nat.add_le_add_right hab 1))
        (fun i u hu => hn (i + 1) u hu)

/-! ## The countable combinatorial data -/

/-- The combinatorial description of a chain: `K` transitions, `K+1` legs with indices
`n : Fin (K+1) → ℕ`, and the path component of each intermediate point in the relevant
intersection `U n_i ∩ U n_{i+1}`. -/
abbrev CData (U : ℕ → Set X) (x₀ x : X) : Type _ :=
  { p : Σ K : ℕ, Σ n : (Fin (K + 1) → ℕ),
      ((j : Fin K) → ZerothHomotopy ↥(U (n j.castSucc) ∩ U (n (Fin.succ j)))) //
    x₀ ∈ U (p.2.1 0) ∧ x ∈ U (p.2.1 (Fin.last p.1)) }

namespace CData

variable {U : ℕ → Set X} {x₀ x : X}

abbrev K (p : CData U x₀ x) : ℕ := p.1.1

abbrev n (p : CData U x₀ x) : Fin (p.K + 1) → ℕ := p.1.2.1

abbrev C (p : CData U x₀ x) :
    (j : Fin p.K) → ZerothHomotopy ↥(U (p.n j.castSucc) ∩ U (p.n (Fin.succ j))) := p.1.2.2

theorem h0 (p : CData U x₀ x) : x₀ ∈ U (p.n 0) := p.2.1

theorem hx (p : CData U x₀ x) : x ∈ U (p.n (Fin.last p.K)) := p.2.2

/-- A representative point of a path component of a set. -/
noncomputable def rep {W : Set X} (C : ZerothHomotopy ↥W) : ↥W := Quotient.out C

theorem rep_mk {W : Set X} (C : ZerothHomotopy ↥W) : ZerothHomotopy.mk (rep C) = C :=
  Quotient.out_eq C

/-- The point of `X` attached to the `i`-th vertex of the chain: the `i`-th transition point, and
`x` for the last vertex. -/
noncomputable def legY (p : CData U x₀ x) : Fin (p.K + 1) → X :=
  Fin.lastCases x (fun j : Fin p.K => (rep (p.C j)).1)

theorem legY_last (p : CData U x₀ x) : p.legY (Fin.last p.K) = x := by
  simp [legY]

theorem legY_castSucc (p : CData U x₀ x) (j : Fin p.K) :
    p.legY j.castSucc = (rep (p.C j)).1 := by
  simp [legY]

theorem legY_castSucc_mem (p : CData U x₀ x) (j : Fin p.K) :
    p.legY j.castSucc ∈ U (p.n j.castSucc) ∧ p.legY j.castSucc ∈ U (p.n (Fin.succ j)) := by
  rw [p.legY_castSucc j]
  exact ⟨(rep (p.C j)).2.1, (rep (p.C j)).2.2⟩

/-- The list of moves determined by the combinatorial data. -/
noncomputable def legList (p : CData U x₀ x) : List (ℕ × X) :=
  List.ofFn (fun i : Fin (p.K + 1) => (p.n i, p.legY i))

theorem legList_eq (p : CData U x₀ x) :
    p.legList = List.ofFn (fun i : Fin (p.K + 1) => (p.n i, p.legY i)) := rfl

theorem legList_length (p : CData U x₀ x) : p.legList.length = p.K + 1 := by
  rw [legList, List.length_ofFn]

/-- Each move of the combinatorial chain is legitimate. -/
theorem valid_aux {hU : DiscCover U} {x₀ : X} :
    ∀ (K : ℕ) (n : Fin (K + 1) → ℕ) (w : Fin (K + 1) → X) (e : UC x₀),
      e.pt ∈ U (n 0) →
      (∀ i : Fin K, w i.castSucc ∈ U (n i.castSucc) ∧ w i.castSucc ∈ U (n (Fin.succ i))) →
      w (Fin.last K) ∈ U (n (Fin.last K)) →
      Valid U hU e (List.ofFn (fun i : Fin (K+1) => (n i, w i))) ∧
        (chainPt U hU (List.ofFn (fun i : Fin (K+1) => (n i, w i))) e).pt = w (Fin.last K) := by
  intro K
  induction K with
  | zero =>
      intro n w e he htr hlast
      rw [List.ofFn_succ, List.ofFn_zero, chainPt_cons, chainPt_nil]
      refine ⟨⟨by simpa using he, by simpa using hlast, trivial⟩, ?_⟩
      rw [step_pt ⟨by simpa using he, by simpa using hlast⟩]
      simpa using hlast
  | succ K ih =>
      intro n w e he htr hlast
      rw [List.ofFn_succ, chainPt_cons]
      have hhead : w (0 : Fin (K+2)) ∈ U (n (0 : Fin (K+2))) := by
        simpa using (htr 0).1
      have hmid : (step U hU e (n 0) (w 0)).pt ∈ U (n (Fin.succ 0)) := by
        rw [step_pt ⟨by simpa using he, by simpa using hhead⟩]
        simpa using (htr 0).2
      obtain ⟨ihv, ihp⟩ := ih (fun i : Fin (K+1) => n i.succ) (fun i : Fin (K+1) => w i.succ)
        (step U hU e (n 0) (w 0)) hmid
        (fun i : Fin K => ⟨by simpa using (htr i.succ).1, by simpa using (htr i.succ).2⟩)
        (by simpa using hlast)
      exact ⟨⟨by simpa using he, by simpa using hhead, ihv⟩, by simpa using ihp⟩

/-- The list of moves of the combinatorial chain is valid, and its last move ends at `x`. -/
theorem valid_legList {hU : DiscCover U} (p : CData U x₀ x) :
    Valid U hU (UC.base x₀) (List.ofFn (fun i : Fin (p.K + 1) => (p.n i, p.legY i))) ∧
      (chainPt U hU (List.ofFn (fun i : Fin (p.K + 1) => (p.n i, p.legY i))) (UC.base x₀)).pt = x := by
  have hA := valid_aux (hU := hU) p.K p.n p.legY (UC.base x₀) p.h0
    (fun j : Fin p.K => p.legY_castSucc_mem j)
    (by rw [p.legY_last]; exact p.hx)
  exact ⟨hA.1, by rw [hA.2, p.legY_last]⟩

/-- The point of the universal cover reached by the combinatorial chain. -/
noncomputable def pt (hU : DiscCover U) (p : CData U x₀ x) : UC x₀ :=
  chainPt U hU p.legList (UC.base x₀)

theorem pt_pt (hU : DiscCover U) (p : CData U x₀ x) : (p.pt hU).pt = x := by
  rw [pt, show p.legList = List.ofFn (fun i : Fin (p.K + 1) => (p.n i, p.legY i)) from rfl]
  exact (p.valid_legList (hU := hU)).2

/-- The class of paths from `x₀` to `x` represented by the combinatorial chain. -/
noncomputable def quot (hU : DiscCover U) (p : CData U x₀ x) : Path.Homotopic.Quotient x₀ x :=
  (p.pt hU).cls.cast rfl (p.pt_pt hU).symm

/-- The combinatorial data is countable. -/
theorem countable_CData {x₀ x : X} [SecondCountableTopology X] [LocallyPathConnectedSpace X]
    (hU : DiscCover U) : Countable (CData U x₀ x) := by
  haveI : ∀ a b : ℕ, Countable (ZerothHomotopy ↥(U a ∩ U b)) := fun a b =>
    countable_zerothHomotopy ((hU.1 a).isOpen.inter (hU.1 b).isOpen)
  infer_instance

end CData

/-! ## Every class of paths is represented by combinatorial data -/

open CData

theorem legY_mem {U : ℕ → Set X} {x₀ x : X} (p : CData U x₀ x) (px : x ∈ U (p.n (Fin.last p.K))) (i : Fin (p.K + 1)) :
    p.legY i ∈ U (p.n i) := by
  induction i using Fin.lastCases with
  | last => rw [p.legY_last]; exact px
  | cast j => rw [p.legY_castSucc j]; exact (rep (p.C j)).2.1

theorem surjective_quot {U : ℕ → Set X} {x₀ x : X} (hU : DiscCover U) :
    Function.Surjective (fun p : CData U x₀ x => p.quot hU) := by
  intro q
  set γ : Path x₀ x := q.out with hγdef
  have hq : Path.Homotopic.Quotient.mk γ = q := Quotient.out_eq q
  obtain ⟨t, ht0, htmono, hMe, hcov⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun n : ℕ => γ ⁻¹' (U n)) (fun n => (hU.1 n).isOpen.preimage γ.continuous)
      (by
        intro u _
        have hu : γ u ∈ ⋃ n, U n := by rw [hU.2]; exact Set.mem_univ _
        simpa using hu)
  obtain ⟨M, hM⟩ := hMe
  choose m hm using hcov
  have htM : t M = 1 := hM M le_rfl
  have htM1 : t (M + 1) = 1 := hM (M + 1) (Nat.le_succ M)
  have hn : ∀ (i : ℕ) (u : I), u ∈ Set.Icc (t i) (t (i + 1)) → γ u ∈ U (m i) :=
    fun i u hu => Set.subset_def.mp (hm i) u hu
  -- the combinatorial data
  let n' : Fin (M + 1) → ℕ := fun i => m i.1
  have hmem_int : ∀ j : Fin M, γ (t (j.1 + 1)) ∈ U (m j.1) ∩ U (m (j.1 + 1)) := by
    intro j
    exact ⟨hn j.1 _ ⟨htmono (Nat.le_succ j.1), le_refl _⟩,
      hn (j.1 + 1) _ ⟨le_refl _, htmono (Nat.le_succ (j.1 + 1))⟩⟩
  let comp : (j : Fin M) → ZerothHomotopy ↥(U (n' j.castSucc) ∩ U (n' (Fin.succ j))) :=
    fun j => ZerothHomotopy.mk ⟨γ (t (j.1 + 1)), by simpa [n'] using hmem_int j⟩
  have hx0m : x₀ ∈ U (m 0) := by
    have h := hn 0 (t 0) ⟨le_refl _, htmono (Nat.zero_le 1)⟩
    rwa [show t 0 = 0 from ht0, γ.source] at h
  have hxm : x ∈ U (m M) := by
    have h := hn M (t M) ⟨le_refl _, by rw [htM, htM1]⟩
    rwa [show t M = 1 from htM, γ.target] at h
  let p : CData U x₀ x := ⟨⟨M, ⟨n', comp⟩⟩, by
    refine ⟨?_, ?_⟩
    · simpa [n'] using hx0m
    · simpa [n'] using hxm⟩
  have hpK : p.K = M := rfl
  have hpn : p.n = n' := rfl
  have hpC : p.C = comp := rfl
  refine ⟨p, ?_⟩
  -- the chain of the subdivision
  have hchain : chainPt U hU (List.ofFn (fun i : Fin (M + 1) => (n' i, γ (t (i.1 + 1)))))
      (UC.base x₀) = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) := by
    rw [show UC.base x₀ = UC.segPt γ (t 0) from by rw [ht0]; exact (ucSegPt_zero γ).symm]
    rw [chainPt_ofFn_segPt (U := U) (hU := hU) γ (M + 1) t m htmono hn]
    rw [htM1]
    exact ucSegPt_one γ
  -- the invariance
  have hinv : chainPt U hU (List.ofFn (fun i : Fin (M + 1) => (n' i, p.legY i))) (UC.base x₀)
      = chainPt U hU (List.ofFn (fun i : Fin (M + 1) => (n' i, γ (t (i.1 + 1))))) (UC.base x₀) := by
    refine chainPt_invariant (U := U) (hU := hU) (UC.base x₀) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [List.length_ofFn, List.length_ofFn]
    · intro i hi
      rw [List.getElem_ofFn, List.getElem_ofFn]
    · intro r hr
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      have hnM : p.n (Fin.last p.K) = m M := rfl
      exact legY_mem p (by rw [hnM]; exact hxm) i
    · intro r hr
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact hn i.1 _ ⟨htmono (Nat.le_succ i.1), le_refl _⟩
    · intro i hi
      have hiM : i < M := by
        rw [List.length_ofFn] at hi
        omega
      have hiK : i < p.K := hiM
      have hi2 : i + 1 < M + 1 := by
        rw [List.length_ofFn] at hi
        exact hi
      rw [List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
      simp only [Prod.fst, Prod.snd]
      have h1 : p.legY (⟨i, by omega⟩ : Fin (p.K + 1)) = (rep (p.C (⟨i, hiK⟩ : Fin p.K))).1 := by
        rw [show (⟨i, by omega⟩ : Fin (p.K + 1)) = (⟨i, hiK⟩ : Fin p.K).castSucc from rfl,
          p.legY_castSucc]
      rw [h1]
      refine (joinedIn_iff_joined (rep (p.C (⟨i, hiK⟩ : Fin p.K))).2
        (hmem_int ⟨i, hiK⟩)).mpr ?_
      have hCe : p.C (⟨i, hiK⟩ : Fin p.K) = ZerothHomotopy.mk
          (⟨γ (t (i + 1)), (hmem_int ⟨i, hiK⟩)⟩ :
            ↥(U (n' (⟨i, hiK⟩ : Fin p.K).castSucc) ∩ U (n' (Fin.succ (⟨i, hiK⟩ : Fin p.K))))) := rfl
      rw [hCe]
      have hC : ZerothHomotopy.mk (rep (ZerothHomotopy.mk (⟨γ (t (i + 1)), (hmem_int ⟨i, hiK⟩)⟩ :
            ↥(U (n' (⟨i, hiK⟩ : Fin p.K).castSucc) ∩ U (n' (Fin.succ (⟨i, hiK⟩ : Fin p.K)))))))
          = ZerothHomotopy.mk (⟨γ (t (i + 1)), (hmem_int ⟨i, hiK⟩)⟩ :
            ↥(U (n' (⟨i, hiK⟩ : Fin p.K).castSucc) ∩ U (n' (Fin.succ (⟨i, hiK⟩ : Fin p.K))))) :=
        rep_mk _
      exact Quotient.exact hC
    · have h1 : (List.ofFn (fun i : Fin (M + 1) => (n' i, p.legY i))).getLast?
          = some (n' (Fin.last M), p.legY (Fin.last M)) := by
        rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]
        simp
      have h2 : (List.ofFn (fun i : Fin (M + 1) => (n' i, γ (t (i.1 + 1))))).getLast?
          = some (n' (Fin.last M), γ (t (M + 1))) := by
        rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]
        simp
      rw [h1, h2]
      congr 2
      exact (show p.legY (Fin.last M) = x from p.legY_last).trans
        (show x = γ (t (M + 1)) from by rw [htM1, γ.target])
  have hpe : p.pt hU = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) := by
    rw [CData.pt, show p.legList = List.ofFn (fun i : Fin (M + 1) => (n' i, p.legY i)) from rfl]
    exact hinv.trans hchain
  have hpt : (p.pt hU).pt = x := by rw [hpe]
  have hcls : p.quot hU = Path.Homotopic.Quotient.mk γ := by
    have h2 : (⟨(p.pt hU).pt, (p.pt hU).cls⟩ : UC x₀)
        = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) := hpe
    rw [UC.mk.injEq] at h2
    rw [CData.quot]
    exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq rfl hpt.symm).trans h2.2)
  rw [← hq]
  exact hcls

/-! ## The main theorem: countably many homotopy classes -/

theorem countable_homotopicQuotient {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyPathConnectedSpace X] {x₀ x : X} {U : ℕ → Set X} (hU : DiscCover U) :
    Countable (Path.Homotopic.Quotient x₀ x) := by
  haveI hc : Countable (CData U x₀ x) := CData.countable_CData (U := U) (x₀ := x₀) (x := x) hU
  exact (surjective_quot (U := U) (x₀ := x₀) (x := x) hU).countable

end Work.EQ.UnivCover
