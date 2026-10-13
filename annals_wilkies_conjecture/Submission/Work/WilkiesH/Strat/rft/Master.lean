import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesH.Strat.rft.ThinSource

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilkiesH.Strat
open WilkiesDesign WilkiesConjecture
open Work.WilG5
variable {S : WilkiesDesign.SOMin}

/-- **Master step.**  The image of a graph over `ℝᵐ` has dimension at most `m`. -/
theorem master (hcd : S.SharpCD) (m : ℕ)
    (ih : ∀ m' < m, ∀ (t : ℕ) (G : Set (Fin (m' + t) → ℝ)) (F D : ℕ),
      G ∈ S.Ω F D (m' + t) → GraphOver m' G → WilkiesDesign.DimLE (lastN t G) m') :
    ∀ (t : ℕ) (G : Set (Fin (m + t) → ℝ)) (F D : ℕ), G ∈ S.Ω F D (m + t) →
      GraphOver m G → WilkiesDesign.DimLE (lastN t G) m := by
  intro t G F D hG hgr
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `m = 0`: a graph over `ℝ⁰` is a subsingleton, and so is every projection of it
    subst hm0
    intro e
    have hsub : ((fun y : Fin t → ℝ => y ∘ e) '' lastN t G).Subsingleton := by
      rintro u ⟨y, hy, rfl⟩ v ⟨y', hy', rfl⟩
      obtain ⟨x, hx⟩ := hy
      obtain ⟨x', hx'⟩ := hy'
      have h1 : Fin.append x y = Fin.append x' y' := hgr _ hx _ hx' (fun i => i.elim0)
      exact congrArg (fun w => w ∘ e) (eq_of_append h1).2
    exact interior_eq_empty_of_subsingleton' (n := 0 + 1)
      (X := (fun y : Fin t → ℝ => y ∘ e) '' lastN t G) (by omega) hsub
  · -- `m ≥ 1`
    intro e
    by_contra hfat
    obtain ⟨w₁, hw₁⟩ := Set.nonempty_iff_ne_empty.mpr hfat
    obtain ⟨ε, hε, hbox⟩ := mem_interior_iff_boxAround.mp hw₁
    -- the source slices, indexed by the extra coordinate `e (Fin.last m)`
    set Src : ℝ → Set (Fin m → ℝ) := fun c =>
      {x | ∃ y : Fin t → ℝ, Fin.append x y ∈ G ∧ y (e (Fin.last m)) = c} with hSrc
    have hdisj : ∀ c ∈ Set.Ioo (w₁ (Fin.last m) - ε) (w₁ (Fin.last m) + ε),
        ∀ c' ∈ Set.Ioo (w₁ (Fin.last m) - ε) (w₁ (Fin.last m) + ε), c ≠ c' →
        Disjoint (Src c) (Src c') := by
      intro c _ c' _ hne
      rw [Set.disjoint_left]
      rintro x ⟨y, hy, hyc⟩ ⟨y', hy', hy'c⟩
      have h1 : Fin.append x y = Fin.append x y' :=
        hgr _ hy _ hy' (fun i => by rw [append_castAdd, append_castAdd])
      exact hne (by rw [← hyc, ← hy'c, (eq_of_append h1).2])
    obtain ⟨c, hc, hcthin⟩ :=
      existsThinLevel (w₁ (Fin.last m) - ε) (w₁ (Fin.last m) + ε) (by linarith) Src hdisj
    have hcmem : |c - w₁ (Fin.last m)| < ε := by
      rw [abs_lt]
      exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
    -- the sliced graph
    set Gc : Set (Fin (m + t) → ℝ) :=
      {z | z ∈ G ∧ z (Fin.natAdd m (e (Fin.last m))) = c} with hGc
    have hGc_mem : Gc ∈ S.Ω (max F (4 * (m + t) + 16) + 1) (D + 4) (m + t) :=
      inter_two_mem (S := S) hG (eq_coord_mem (m + t) (Fin.natAdd m (e (Fin.last m))) c)
    have hGc_gr : GraphOver m Gc := fun z hz z' hz' h => hgr z hz.1 z' hz'.1 h
    have hGc_src : projN t Gc = Src c := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, hy.1, by simpa using hy.2⟩
      · rintro ⟨y, hyG, hyc⟩
        exact ⟨y, ⟨hyG, by simpa using hyc⟩⟩
    have hthin : interior (projN t Gc) = ∅ := by rw [hGc_src]; exact hcthin
    have hlast := thin_source (S := S) hcd m ih t Gc _ _ hGc_mem hGc_gr hthin
    -- the corresponding projection of the sliced image still contains a box
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
    have hinj : Function.Injective (fun i : Fin (m - 1 + 1) => e (Fin.castSucc (Fin.cast hm1 i))) :=
      fun a b hab =>
        Fin.cast_injective hm1 (Fin.castSucc_injective m (e.injective hab))
    have hlast' : interior ((fun y : Fin t → ℝ =>
        y ∘ (fun i : Fin (m - 1 + 1) => e (Fin.castSucc (Fin.cast hm1 i)))) '' lastN t Gc) = ∅ :=
      hlast ⟨_, hinj⟩
    have hbox' : ∀ w : Fin (m - 1 + 1) → ℝ,
        (∀ i, |w i - w₁ (Fin.castSucc (Fin.cast hm1 i))| < ε) →
        w ∈ (fun y : Fin t → ℝ =>
          y ∘ (fun i : Fin (m - 1 + 1) => e (Fin.castSucc (Fin.cast hm1 i)))) '' lastN t Gc := by
      intro w hw
      set z : Fin t → ℝ := Function.extend (fun i : Fin (m - 1 + 1) => e (Fin.castSucc (Fin.cast hm1 i)))
        w (fun j' : Fin t => if j' = e (Fin.last m) then c else 0) with hz
      have hzapply : ∀ i : Fin (m - 1 + 1), z (e (Fin.castSucc (Fin.cast hm1 i))) = w i :=
        fun i => Function.Injective.extend_apply hinj w _ i
      have hnot : ¬ ∃ i : Fin (m - 1 + 1), e (Fin.castSucc (Fin.cast hm1 i)) = e (Fin.last m) := by
        rintro ⟨i, hi⟩
        exact absurd (e.injective hi) (ne_of_lt (Fin.castSucc_lt_last (Fin.cast hm1 i)))
      have hzlast : z (e (Fin.last m)) = c := by
        rw [hz, Function.extend_apply' w (fun j' : Fin t => if j' = e (Fin.last m) then c else 0)
          (e (Fin.last m)) hnot]
        simp
      have hzbox : (fun i : Fin (m + 1) => z (e i)) ∈ boxAround w₁ ε := by
        rw [mem_boxAround]
        intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · have hj : Fin.cast hm1 (Fin.cast hm1.symm j) = j := Fin.ext rfl
          rw [← hj, hzapply]
          simpa [hj] using hw (Fin.cast hm1.symm j)
        · rw [hzlast]; exact hcmem
      have hzG : (fun i : Fin (m + 1) => z (e i)) ∈
          (fun y : Fin t → ℝ => y ∘ ⇑e) '' lastN t G := hbox hzbox
      obtain ⟨y, hy, hyz⟩ := hzG
      refine ⟨y, ?_, ?_⟩
      · obtain ⟨x, hx⟩ := hy
        refine ⟨x, hx, ?_⟩
        have h2 : (fun i : Fin (m + 1) => z (e i)) (Fin.last m) = c := hzlast
        have h3 : y (e (Fin.last m)) = c := by
          simpa [Function.comp_apply, h2] using congrFun hyz (Fin.last m)
        simpa using h3
      · funext i
        show y (e (Fin.castSucc (Fin.cast hm1 i))) = w i
        rw [show y (e (Fin.castSucc (Fin.cast hm1 i))) = z (e (Fin.castSucc (Fin.cast hm1 i))) from
          congrFun hyz (Fin.castSucc (Fin.cast hm1 i)), hzapply i]
    have hne : (interior ((fun y : Fin t → ℝ =>
        y ∘ (fun i : Fin (m - 1 + 1) => e (Fin.castSucc (Fin.cast hm1 i)))) '' lastN t Gc)).Nonempty :=
      ⟨fun i => w₁ (Fin.castSucc (Fin.cast hm1 i)),
        interior_maximal (fun w hw => hbox' w (mem_boxAround.mp hw))
        (isOpen_boxAround _ _) (mem_boxAround.mpr fun i => by rw [sub_self, abs_zero]; exact hε)⟩
    rw [hlast'] at hne
    exact Set.not_nonempty_empty hne

/-- **The dimension theorem for `Ω`-graphs**: the image of a definable graph over `ℝᵐ` has
dimension at most `m`; if its source is thin, the image has dimension at most `m - 1`. -/
theorem dimLE_of_graphOver (hcd : S.SharpCD) :
    ∀ (m t F D : ℕ) (G : Set (Fin (m + t) → ℝ)), G ∈ S.Ω F D (m + t) →
      GraphOver m G →
      WilkiesDesign.DimLE (lastN t G) m ∧
        (interior (projN t G) = ∅ → WilkiesDesign.DimLE (lastN t G) (m - 1)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have ih1 : ∀ m' < m, ∀ (t : ℕ) (G : Set (Fin (m' + t) → ℝ)) (F D : ℕ),
        G ∈ S.Ω F D (m' + t) → GraphOver m' G → WilkiesDesign.DimLE (lastN t G) m' :=
      fun m' hm' t G F D hG hgr => (ih m' hm' t F D G hG hgr).1
    refine fun t F D G hG hgr => ⟨master (S := S) hcd m ih1 t G F D hG hgr, ?_⟩
    exact thin_source (S := S) hcd m ih1 t G F D hG hgr


end Work.WilkiesH.Strat
