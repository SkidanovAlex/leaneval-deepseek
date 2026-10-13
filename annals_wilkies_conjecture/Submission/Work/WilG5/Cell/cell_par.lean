/-
  WilG5 — cell parametrisation, by induction on the ambient dimension.

  For a non-empty cell `κ ⊆ [0,1]^n` (an `IsCell` proof), of format `F` and degree `D`, there is a
  `Ω`-definable relation `R ⊆ ℝ^{d+n}` (`d ≤ n` the number of band levels of the cell, `e` the
  free coordinates) which `CellPar`-parametrises `κ`.

  The relation is built *directly from `κ` and `e`* (no convex combinations): with `p ∈ κ` an
  arbitrary chosen point,

    `R := {z | z.tail ∈ κ ∧ (∀ i, z (natAdd d (e i)) = z (castAdd n i))}`
         `∪ {z | z.first d ∈ openCube d ∧ z.first d ∉ coordImage e κ ∧ z.tail = p}`,

  which is `Work.WilG5.Cell.cellRel e κ p`; its `Ω`-degree is linear in `D` with coefficient `2`
  (`cellRel_mem`).  The induction supplies the free coordinates `e` and proves the strengthened
  predicate `CellParI` (CellPar plus injectivity of `x ↦ x ∘ e` on `κ`), from which `CellPar`
  follows.
-/
import Mathlib
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.Cell.cellRel_def
import Submission.Work.WilG5.Cell.ereal_margin
import Submission.Work.WilG5.Cell.contOn_abs_lt
import Submission.Work.WilG5.Cell.contOn_ereal_lt
import Submission.Work.WilG5.Cell.contOn_ereal_gt
import Submission.Work.WilG5.Cell.fibre_strict

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG5.Cell

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-! ## 0. The strengthened parametrisation predicate -/

/-- `CellPar` together with injectivity of the free-coordinate map `x ↦ x ∘ e` on `κ`. -/
def CellParI (n : ℕ) (κ : Set (Fin n → ℝ)) (d : ℕ) (e : Fin d → Fin n)
    (R : Set (Fin (d + n) → ℝ)) : Prop :=
  Work.WilG5.CellPar n κ d e R ∧ Set.InjOn (fun x : Fin n → ℝ => x ∘ e) κ

theorem cellPar_of_cellParI {n d : ℕ} {κ : Set (Fin n → ℝ)} {e : Fin d → Fin n}
    {R : Set (Fin (d + n) → ℝ)} (h : CellParI n κ d e R) : Work.WilG5.CellPar n κ d e R := h.1

theorem openCube_zero : openCube 0 = (Set.univ : Set (Fin 0 → ℝ)) := by
  ext t
  simp only [openCube, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact fun i => Fin.elim0 i

/-! ## 1. The clauses of `CellPar` that do not depend on the cell structure -/

theorem cellRel_clause1 {n d : ℕ} {κ : Set (Fin n → ℝ)} {e : Fin d → Fin n} {p : Fin n → ℝ}
    (hp : p ∈ κ) : ∀ u ∈ openCube d, ∀ x : Fin n → ℝ, Fin.append u x ∈ cellRel e κ p → x ∈ κ := by
  intro u hu x hx
  rcases (cellRel_mem_iff e κ p u x).mp hx with ⟨hxk, _⟩ | ⟨_, _, hxp⟩
  · exact hxk
  · rw [hxp]; exact hp

theorem cellRel_clause3 {n d : ℕ} {κ : Set (Fin n → ℝ)} {e : Fin d → Fin n} {p : Fin n → ℝ} :
    ∀ u ∈ openCube d, ∃ x : Fin n → ℝ, Fin.append u x ∈ cellRel e κ p := by
  intro u hu
  by_cases hmem : u ∈ Work.WilG5.coordImage e κ
  · obtain ⟨x, hxk, hxe⟩ := hmem
    exact ⟨x, (cellRel_mem_iff e κ p u x).mpr (Or.inl ⟨hxk, hxe⟩)⟩
  · exact ⟨p, (cellRel_mem_iff e κ p u p).mpr (Or.inr ⟨hu, hmem, rfl⟩)⟩

theorem cellRel_clause4 {n d : ℕ} {κ : Set (Fin n → ℝ)} {e : Fin d → Fin n} {p : Fin n → ℝ}
    (h5 : ∀ x ∈ κ, x ∘ e ∈ openCube d) :
    ∀ x ∈ κ, ∃ u ∈ openCube d, Fin.append u x ∈ cellRel e κ p := by
  intro x hx
  exact ⟨x ∘ e, h5 x hx, (cellRel_mem_iff e κ p (x ∘ e) x).mpr (Or.inl ⟨hx, rfl⟩)⟩

/-! ## 2. The graph step -/

theorem cell_par_graph {n : ℕ} (K' L' : ℕ)
    (hIH : ∀ (F D : ℕ) (C : Set (Fin n → ℝ)), IsCell n C → C.Nonempty → C ⊆ cube01 n →
      C ∈ S.Ω F D n → ∃ (d : ℕ) (e : Fin d → Fin n) (R : Set (Fin (d + n) → ℝ)),
        d ≤ n ∧ R ∈ S.Ω (F + K') (2 * D + L') (d + n) ∧ CellParI n C d e R)
    {F D : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} {κ : Set (Fin (n + 1) → ℝ)}
    (hC : IsCell n C) (hf : ContinuousOn f C)
    (hκ : κ = {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)})
    (hne : κ.Nonempty) (hsub : κ ⊆ cube01 (n + 1)) (hΩ : κ ∈ S.Ω F D (n + 1)) :
    ∃ (d : ℕ) (e : Fin d → Fin (n + 1)) (R : Set (Fin (d + (n + 1)) → ℝ)),
      d ≤ n + 1 ∧ R ∈ S.Ω (F + (2000 * (n + 1) + 4000)) (2 * D + (2000 * (n + 1) + 4000))
        (d + (n + 1)) ∧ CellParI (n + 1) κ d e R := by
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    rw [hκ] at hx
    exact ⟨Fin.init x, hx.1⟩
  have hCsub : C ⊆ cube01 n := by
    intro y hy
    have hyκ : Fin.snoc y (f y) ∈ κ := by
      rw [hκ]
      exact ⟨by rw [Fin.init_snoc]; exact hy, by rw [Fin.snoc_last, Fin.init_snoc]⟩
    have hyc := hsub hyκ
    intro i
    have := hyc (Fin.castSucc i)
    rwa [Fin.snoc_castSucc] at this
  have hCΩ : C ∈ S.Ω (F + 1) D n := by
    have hproj := S.proj hΩ
    have heq : projLast κ = C := by
      ext x
      constructor
      · rintro ⟨t, ht⟩
        rw [hκ] at ht
        simpa only [Fin.init_snoc] using ht.1
      · intro hx
        refine ⟨f x, ?_⟩
        rw [hκ]
        exact ⟨by rw [Fin.init_snoc]; exact hx, by rw [Fin.snoc_last, Fin.init_snoc]⟩
    rwa [heq] at hproj
  obtain ⟨d, e, R', hdle, hR'mem, hparI⟩ := hIH (F + 1) D C hC hCne hCsub hCΩ
  obtain ⟨hpar, hinj⟩ := hparI
  rcases hpar with ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
  obtain ⟨p, hp⟩ := hne
  have hmain : ∀ x ∈ κ, Fin.init x ∈ C := by
    intro x hx; rw [hκ] at hx; exact hx.1
  have hlast : ∀ x ∈ κ, x (Fin.last n) = f (Fin.init x) := by
    intro x hx; rw [hκ] at hx; exact hx.2
  have h5 : ∀ x ∈ κ, x ∘ embCastSucc e ∈ openCube d := by
    intro x hx
    have heq : x ∘ embCastSucc e = Fin.init x ∘ e := by ext i; rfl
    rw [heq]
    exact hc5 (Fin.init x) (hmain x hx)
  refine ⟨d, embCastSucc e, cellRel (embCastSucc e) κ p, hdle.trans (Nat.le_succ n), ?_, ?_⟩
  · refine Work.WilG5.mem_mono (cellRel_mem (S := S) F D hΩ (embCastSucc e) p)
      (F + (2000 * (n + 1) + 4000)) (2 * D + (2000 * (n + 1) + 4000)) ?_ ?_ <;> omega
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact cellRel_clause1 hp
    · intro u hu x y hx hy
      rcases (cellRel_mem_iff (embCastSucc e) κ p u x).mp hx with ⟨hxk, hxe⟩ | ⟨huc, hnot, hxp⟩
      · rcases (cellRel_mem_iff (embCastSucc e) κ p u y).mp hy with ⟨hyk, hye⟩ | ⟨huc2, hnot2, hyp⟩
        · have hinit : Fin.init x = Fin.init y := by
            refine hinj (hmain x hxk) (hmain y hyk) ?_
            show Fin.init x ∘ e = Fin.init y ∘ e
            have e1 : Fin.init x ∘ e = x ∘ embCastSucc e := by ext i; rfl
            have e2 : Fin.init y ∘ e = y ∘ embCastSucc e := by ext i; rfl
            rw [e1, e2, hxe, hye]
          have hl : x (Fin.last n) = y (Fin.last n) := by rw [hlast x hxk, hlast y hyk, hinit]
          calc x = Fin.snoc (Fin.init x) (x (Fin.last n)) := (Fin.snoc_init_self x).symm
            _ = Fin.snoc (Fin.init y) (y (Fin.last n)) := by rw [hinit, hl]
            _ = y := Fin.snoc_init_self y
        · exact absurd ⟨x, hxk, hxe⟩ hnot2
      · rcases (cellRel_mem_iff (embCastSucc e) κ p u y).mp hy with ⟨hyk, hye⟩ | ⟨huc2, hnot2, hyp⟩
        · exact absurd ⟨y, hyk, hye⟩ hnot
        · rw [hxp, hyp]
    · exact cellRel_clause3
    · exact cellRel_clause4 h5
    · exact h5
    · intro y hyk η hη
      obtain ⟨δf, hδfpos, hδf⟩ := contOn_abs_lt (n := n) hf (hmain y hyk) hη
      obtain ⟨ε, hεpos, hε⟩ := hc6 (Fin.init y) (hmain y hyk) (min η δf) (lt_min hη hδfpos)
      refine ⟨ε, hεpos, ?_⟩
      intro v hv hvclose
      have hvclose' : ∀ i : Fin d, |v i - Fin.init y (e i)| < ε := by
        intro i
        have hthis := hvclose i
        simpa only [embCastSucc, Fin.init] using hthis
      obtain ⟨z', hz'R, hz'close, hz'eq⟩ := hε v hv hvclose'
      refine ⟨Fin.snoc z' (f z'), ?_, ?_, ?_⟩
      · refine (cellRel_mem_iff (embCastSucc e) κ p v (Fin.snoc z' (f z'))).mpr
          (Or.inl ⟨?_, ?_⟩)
        · rw [hκ]
          exact ⟨by rw [Fin.init_snoc]; exact hc1 v hv z' hz'R, by rw [Fin.snoc_last, Fin.init_snoc]⟩
        · ext i
          simp only [Function.comp_apply, embCastSucc, Fin.snoc_castSucc]
          exact hz'eq i
      · intro j
        by_cases hj : j = Fin.last n
        · subst hj
          rw [Fin.snoc_last, hlast y hyk]
          refine hδf z' (hc1 v hv z' hz'R) ?_
          intro i
          exact lt_of_lt_of_le (hz'close i) (min_le_right η δf)
        · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
          rw [Fin.snoc_castSucc]
          exact lt_of_lt_of_le (hz'close j') (min_le_left η δf)
      · intro i
        simp only [embCastSucc, Fin.snoc_castSucc]
        exact hz'eq i
    · intro x hx y hy hxy
      have hinit : Fin.init x = Fin.init y := by
        refine hinj (hmain x hx) (hmain y hy) ?_
        show Fin.init x ∘ e = Fin.init y ∘ e
        have e1 : Fin.init x ∘ e = x ∘ embCastSucc e := by ext i; rfl
        have e2 : Fin.init y ∘ e = y ∘ embCastSucc e := by ext i; rfl
        rw [e1, e2]
        exact hxy
      have hl : x (Fin.last n) = y (Fin.last n) := by rw [hlast x hx, hlast y hy, hinit]
      calc x = Fin.snoc (Fin.init x) (x (Fin.last n)) := (Fin.snoc_init_self x).symm
        _ = Fin.snoc (Fin.init y) (y (Fin.last n)) := by rw [hinit, hl]
        _ = y := Fin.snoc_init_self y

/-! ## 3. The band step -/

theorem cell_par_band {n : ℕ} (K' L' : ℕ)
    (hIH : ∀ (F D : ℕ) (C : Set (Fin n → ℝ)), IsCell n C → C.Nonempty → C ⊆ cube01 n →
      C ∈ S.Ω F D n → ∃ (d : ℕ) (e : Fin d → Fin n) (R : Set (Fin (d + n) → ℝ)),
        d ≤ n ∧ R ∈ S.Ω (F + K') (2 * D + L') (d + n) ∧ CellParI n C d e R)
    {F D : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal} {κ : Set (Fin (n + 1) → ℝ)}
    (hC : IsCell n C) (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x)
    (hκ : κ = {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < (((z (Fin.last n) : ℝ)) : EReal) ∧
      (((z (Fin.last n) : ℝ)) : EReal) < b (Fin.init z)})
    (hne : κ.Nonempty) (hsub : κ ⊆ cube01 (n + 1)) (hΩ : κ ∈ S.Ω F D (n + 1)) :
    ∃ (d : ℕ) (e : Fin d → Fin (n + 1)) (R : Set (Fin (d + (n + 1)) → ℝ)),
      d ≤ n + 1 ∧ R ∈ S.Ω (F + (2000 * (n + 1) + 4000)) (2 * D + (2000 * (n + 1) + 4000))
        (d + (n + 1)) ∧ CellParI (n + 1) κ d e R := by
  have memE : ∀ x ∈ κ, a (Fin.init x) < (((x (Fin.last n) : ℝ)) : EReal) ∧
      (((x (Fin.last n) : ℝ)) : EReal) < b (Fin.init x) := by
    intro x hx; rw [hκ] at hx; exact hx.2
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨Fin.init x, by rw [hκ] at hx; exact hx.1⟩
  have hCsub : C ⊆ cube01 n := by
    intro y hy
    obtain ⟨r, har, hrb⟩ := EReal.exists_between_coe_real (hab y hy)
    have hyκ : Fin.snoc y r ∈ κ := by
      rw [hκ]
      exact ⟨by rw [Fin.init_snoc]; exact hy, by rw [Fin.snoc_last, Fin.init_snoc]; exact har,
        by rw [Fin.snoc_last, Fin.init_snoc]; exact hrb⟩
    have hyc := hsub hyκ
    intro i
    have := hyc (Fin.castSucc i)
    rwa [Fin.snoc_castSucc] at this
  have hCΩ : C ∈ S.Ω (F + 1) D n := by
    have hproj := S.proj hΩ
    have heq : projLast κ = C := by
      ext x
      constructor
      · rintro ⟨t, ht⟩
        rw [hκ] at ht
        simpa only [Fin.init_snoc] using ht.1
      · intro hx
        obtain ⟨r, har, hrb⟩ := EReal.exists_between_coe_real (hab x hx)
        exact ⟨r, by rw [hκ]; exact ⟨by rw [Fin.init_snoc]; exact hx,
          by rw [Fin.snoc_last, Fin.init_snoc]; exact har,
          by rw [Fin.snoc_last, Fin.init_snoc]; exact hrb⟩⟩
    rwa [heq] at hproj
  obtain ⟨d, e, R', hdle, hR'mem, hparI⟩ := hIH (F + 1) D C hC hCne hCsub hCΩ
  obtain ⟨hpar, hinj⟩ := hparI
  rcases hpar with ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
  obtain ⟨p, hp⟩ := hne
  have hmain : ∀ x ∈ κ, Fin.init x ∈ C := by
    intro x hx; rw [hκ] at hx; exact hx.1
  have hlast : ∀ x ∈ κ, (0 : ℝ) < x (Fin.last n) ∧ x (Fin.last n) < 1 :=
    fun x hx => fibre_strict hκ hsub x hx
  have hcomp : ∀ (x : Fin (n + 1) → ℝ), Fin.init x ∘ e = Fin.init (x ∘ embSnoc e) := by
    intro x
    ext i
    simp only [Function.comp_apply, Fin.init, embSnoc_castSucc]
  have h5 : ∀ x ∈ κ, x ∘ embSnoc e ∈ openCube (d + 1) := by
    intro x hx
    have hxl := hlast x hx
    have h1 := hc5 (Fin.init x) (hmain x hx)
    intro i
    by_cases hi : i = Fin.last d
    · subst hi
      rw [Function.comp_apply, embSnoc_last]
      exact hxl
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      show x (embSnoc e (Fin.castSucc j)) ∈ Set.Ioo (0 : ℝ) 1
      rw [embSnoc_castSucc]
      simpa only [Fin.init] using h1 j
  refine ⟨d + 1, embSnoc e, cellRel (embSnoc e) κ p, by omega, ?_, ?_⟩
  · refine Work.WilG5.mem_mono (cellRel_mem (S := S) F D hΩ (embSnoc e) p)
      (F + (2000 * (n + 1) + 4000)) (2 * D + (2000 * (n + 1) + 4000)) ?_ ?_ <;> omega
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact cellRel_clause1 hp
    · intro u hu x y hx hy
      rcases (cellRel_mem_iff (embSnoc e) κ p u x).mp hx with ⟨hxk, hxe⟩ | ⟨huc, hnot, hxp⟩
      · rcases (cellRel_mem_iff (embSnoc e) κ p u y).mp hy with ⟨hyk, hye⟩ | ⟨huc2, hnot2, hyp⟩
        · have hinit : Fin.init x = Fin.init y := by
            refine hinj (hmain x hxk) (hmain y hyk) ?_
            show Fin.init x ∘ e = Fin.init y ∘ e
            rw [hcomp x, hcomp y, hxe, hye]
          have hl : x (Fin.last n) = y (Fin.last n) := by
            have hx' := congrFun hxe (Fin.last d)
            have hy' := congrFun hye (Fin.last d)
            simp only [Function.comp_apply, embSnoc_last] at hx' hy'
            rw [hx', hy']
          calc x = Fin.snoc (Fin.init x) (x (Fin.last n)) := (Fin.snoc_init_self x).symm
            _ = Fin.snoc (Fin.init y) (y (Fin.last n)) := by rw [hinit, hl]
            _ = y := Fin.snoc_init_self y
        · exact absurd ⟨x, hxk, hxe⟩ hnot2
      · rcases (cellRel_mem_iff (embSnoc e) κ p u y).mp hy with ⟨hyk, hye⟩ | ⟨huc2, hnot2, hyp⟩
        · exact absurd ⟨y, hyk, hye⟩ hnot
        · rw [hxp, hyp]
    · exact cellRel_clause3
    · exact cellRel_clause4 h5
    · exact h5
    · intro y hyk η hη
      obtain ⟨har, hbr⟩ := memE y hyk
      have hy' := hmain y hyk
      obtain ⟨τ, hτpos, haτ, hbτ⟩ := ereal_margin har hbr
      obtain ⟨δa, hδapos, hδa⟩ := contOn_ereal_lt ha hy' haτ
      obtain ⟨δb, hδbpos, hδb⟩ := contOn_ereal_gt hb hy' hbτ
      obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
        hc6 (Fin.init y) hy' (min η (min δa δb)) (lt_min hη (lt_min hδapos hδbpos))
      have hminA : min ε₁ (min τ η) ≤ ε₁ := min_le_left ε₁ (min τ η)
      have hminτ : min ε₁ (min τ η) ≤ τ := le_trans (min_le_right ε₁ (min τ η)) (min_le_left τ η)
      have hminη : min ε₁ (min τ η) ≤ η := le_trans (min_le_right ε₁ (min τ η)) (min_le_right τ η)
      have hminδa : min η (min δa δb) ≤ δa :=
        le_trans (min_le_right η (min δa δb)) (min_le_left δa δb)
      have hminδb : min η (min δa δb) ≤ δb :=
        le_trans (min_le_right η (min δa δb)) (min_le_right δa δb)
      have hminη' : min η (min δa δb) ≤ η := min_le_left η (min δa δb)
      refine ⟨min ε₁ (min τ η), lt_min hε₁pos (lt_min hτpos hη), ?_⟩
      intro v hv hvclose
      have hvinit : Fin.init v ∈ openCube d := by
        intro i
        have := hv (Fin.castSucc i)
        simpa only [Fin.init] using this
      have hvclose' : ∀ i : Fin d, |(Fin.init v) i - Fin.init y (e i)| < ε₁ := by
        intro i
        have hthis := hvclose (Fin.castSucc i)
        have h2 : y (embSnoc e (Fin.castSucc i)) = Fin.init y (e i) := by
          simp only [embSnoc_castSucc, Fin.init]
        rw [h2] at hthis
        exact lt_of_lt_of_le hthis hminA
      obtain ⟨z', hz'R, hz'close, hz'eq⟩ := hε₁ (Fin.init v) hvinit hvclose'
      have hz'C : z' ∈ C := hc1 (Fin.init v) hvinit z' hz'R
      have hz'δa : ∀ i : Fin n, |z' i - Fin.init y i| < δa :=
        fun i => lt_of_lt_of_le (hz'close i) hminδa
      have hz'δb : ∀ i : Fin n, |z' i - Fin.init y i| < δb :=
        fun i => lt_of_lt_of_le (hz'close i) hminδb
      have haτ' : a z' < (((y (Fin.last n) - τ : ℝ)) : EReal) := hδa z' hz'C hz'δa
      have hbτ' : (((y (Fin.last n) + τ : ℝ)) : EReal) < b z' := hδb z' hz'C hz'δb
      have hvt : |v (Fin.last d) - y (Fin.last n)| < min ε₁ (min τ η) := by
        have := hvclose (Fin.last d)
        rwa [embSnoc_last] at this
      have hvtτ : |v (Fin.last d) - y (Fin.last n)| < τ := lt_of_lt_of_le hvt hminτ
      have hlt1 : y (Fin.last n) - τ < v (Fin.last d) := by
        have := (abs_lt.mp hvtτ).1; linarith
      have hlt2 : v (Fin.last d) < y (Fin.last n) + τ := by
        have := (abs_lt.mp hvtτ).2; linarith
      refine ⟨Fin.snoc z' (v (Fin.last d)), ?_, ?_, ?_⟩
      · refine (cellRel_mem_iff (embSnoc e) κ p v (Fin.snoc z' (v (Fin.last d)))).mpr
          (Or.inl ⟨?_, ?_⟩)
        · rw [hκ]
          refine ⟨by rw [Fin.init_snoc]; exact hz'C, ?_, ?_⟩
          · rw [Fin.snoc_last, Fin.init_snoc]
            exact lt_trans haτ' (EReal.coe_lt_coe_iff.mpr hlt1)
          · rw [Fin.snoc_last, Fin.init_snoc]
            exact lt_trans (EReal.coe_lt_coe_iff.mpr hlt2) hbτ'
        · ext i
          by_cases hi : i = Fin.last d
          · subst hi
            simp only [Function.comp_apply, embSnoc_last, Fin.snoc_last]
          · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
            simp only [Function.comp_apply, embSnoc_castSucc, Fin.snoc_castSucc]
            exact hz'eq j
      · intro j
        by_cases hj : j = Fin.last n
        · subst hj
          rw [Fin.snoc_last]
          exact lt_of_lt_of_le hvt hminη
        · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
          rw [Fin.snoc_castSucc]
          exact lt_of_lt_of_le (hz'close j') hminη'
      · intro i
        by_cases hi : i = Fin.last d
        · subst hi
          simp only [embSnoc_last, Fin.snoc_last]
        · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
          simp only [embSnoc_castSucc, Fin.snoc_castSucc]
          exact hz'eq j
    · intro x hx y hy hxy
      have hinit : Fin.init x = Fin.init y := by
        refine hinj (hmain x hx) (hmain y hy) ?_
        show Fin.init x ∘ e = Fin.init y ∘ e
        rw [hcomp x, hcomp y]
        exact congrArg Fin.init hxy
      have hl : x (Fin.last n) = y (Fin.last n) := by
        have hx' := congrFun hxy (Fin.last d)
        simp only [Function.comp_apply, embSnoc_last] at hx'
        exact hx'
      calc x = Fin.snoc (Fin.init x) (x (Fin.last n)) := (Fin.snoc_init_self x).symm
        _ = Fin.snoc (Fin.init y) (y (Fin.last n)) := by rw [hinit, hl]
        _ = y := Fin.snoc_init_self y

/-! ## 4. The induction -/

theorem cell_par_aux (S : SOMin) :
    ∀ n, ∃ K L : ℕ, ∀ (F D : ℕ) (κ : Set (Fin n → ℝ)),
      IsCell n κ → κ.Nonempty → κ ⊆ cube01 n → κ ∈ S.Ω F D n →
      ∃ (d : ℕ) (e : Fin d → Fin n) (R : Set (Fin (d + n) → ℝ)),
        d ≤ n ∧ R ∈ S.Ω (F + K) (2 * D + L) (d + n) ∧ CellParI n κ d e R := by
  intro n
  induction n with
  | zero =>
    refine ⟨4, 4, ?_⟩
    intro F D κ hcell hne hsub hΩ
    cases hcell
    refine ⟨0, (Fin.elim0 : Fin 0 → Fin 0), Set.univ, le_refl 0, ?_, ?_⟩
    · exact Work.WilG5.mem_mono (Work.WilG5.univ_mem (S := S) (n := 0))
        (F + 4) (2 * D + 4) (by omega) (by omega)
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro u hu x hx; trivial
      · intro u hu x y hx hy; exact funext fun i => Fin.elim0 i
      · intro u hu; exact ⟨Fin.elim0, trivial⟩
      · intro x hx; exact ⟨Fin.elim0, by rw [openCube_zero]; trivial, trivial⟩
      · intro y hy; rw [openCube_zero]; trivial
      · intro y hy η hη
        exact ⟨1, one_pos,
          fun v hv hv' => ⟨y, trivial, fun j => Fin.elim0 j, fun i => Fin.elim0 i⟩⟩
      · intro x hx y hy hxy; exact funext fun i => Fin.elim0 i
  | succ n ih =>
    obtain ⟨K', L', hIH⟩ := ih
    refine ⟨2000 * (n + 1) + 4000, 2000 * (n + 1) + 4000, ?_⟩
    intro F D κ hcell hne hsub hΩ
    cases hcell with
    | graph hC f hf =>
      exact cell_par_graph (S := S) (n := n) K' L' hIH hC hf rfl hne hsub hΩ
    | band hC a b ha hb hab =>
      exact cell_par_band (S := S) (n := n) K' L' hIH hC ha hb hab rfl hne hsub hΩ

/-! ## 5. The requested theorem -/

theorem cell_par (S : WilkiesDesign.SOMin) :
    ∀ (n F : ℕ), ∃ (A C L : ℕ), ∀ (D : ℕ) (κ : Set (Fin n → ℝ)),
      WilkiesDesign.IsCell n κ → κ.Nonempty → κ ⊆ WilkiesDesign.cube01 n → κ ∈ S.Ω F D n →
      ∃ (d : ℕ) (e : Fin d → Fin n) (R : Set (Fin (d + n) → ℝ)),
        d ≤ n ∧ R ∈ S.Ω A (C * D + L) (d + n) ∧ Work.WilG5.CellPar n κ d e R := by
  intro n F
  obtain ⟨K, L, h⟩ := cell_par_aux S n
  refine ⟨F + K, 2, L, ?_⟩
  intro D κ hcell hne hsub hΩ
  obtain ⟨d, e, R, hdle, hRmem, hparI⟩ := h F D κ hcell hne hsub hΩ
  exact ⟨d, e, R, hdle, hRmem, cellPar_of_cellParI hparI⟩

end Work.WilG5.Cell
