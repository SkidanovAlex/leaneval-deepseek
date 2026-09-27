import Mathlib
import Submission.Work.Whitney.PushDefs
import Submission.Work.Whitney.ambient_glue
import Submission.Work.Whitney.reduce_double_points_abstract
import Submission.Work.Whitney.SignCompare

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

-- ASSEMBLY OF `Work.Whitney.HasCancellation` FROM THE AMBIENT PUSH DATA.
--
-- This is the last piece of the Whitney cancellation that is independent of the (large, in
-- progress) construction of the push itself: given the target-side push data -- an open collar
-- `W₀ ⊆ W` containing `p₂`,`q₂` but neither `p₁` nor `q₁`, an open `O ⊇ f '' frontier W₀` on which
-- the diffeomorphism `ψ` (inverse `σ`) is the identity, and the placement conditions -- produce the
-- modified immersion `f'` with `doubleSet f' = doubleSet f \ {four pairs}` and with `pairDet`
-- unchanged off `W`.
--
-- The modified map is `i y = if y ∈ W₀ then ψ (f y) else f y`; the proof reproduces the gluing
-- step of `Submission/Work/Whitney/ambient_glue.lean` (explicitly, since the later `pairDet` step
-- needs the germ form `i =ᶠ f` off `W`, which is not exposed by `HasManifoldCollarData`), and the
-- set algebra of the double point set from `Work.Whitney.cancel_of_push`
-- (`Submission/Work/Whitney/cancel_double_points_oriented.lean`, copied below as
-- `doubleSet_of_push_aux` because that module cannot currently be imported).
--
-- Engineering: `lean_check`/`lean_tactic` are broken here; use scratch files at the workspace root
-- and `lake env lean F.lean` (batch checks into ONE file).  `ContDiff ℝ ⊤` is *analyticity*;
-- `C^∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`.  Do not edit files that are not yours.

/-- **The double point set algebra of the Whitney push** (verbatim from
`Work.Whitney.cancel_of_push`): if `i` agrees with `f` outside an open collar `W₀ ⊆ W`, is
injective on `W₀`, and the pushed image `i '' W₀` is disjoint from the image of the complement of
`W₀`, then `i` has exactly the double points of `f` with the four pairs `(p₁,p₂)`, `(p₂,p₁)`,
`(q₁,q₂)`, `(q₂,q₁)` removed. -/
theorem doubleSet_of_push_aux {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (W : Set M)
    (p₁ p₂ q₁ q₂ : M)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (W₀ : Set M) (i : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hW₀sub : W₀ ⊆ W)
    (hp₂W₀ : p₂ ∈ W₀) (hq₂W₀ : q₂ ∈ W₀) (hp₁W₀ : p₁ ∉ W₀) (hq₁W₀ : q₁ ∉ W₀)
    (hi_inj : Set.InjOn i W₀)
    (hi_eq : ∀ y : M, y ∉ W₀ → i y = f y)
    (hplace : (i '' W₀) ∩ (f '' W₀ᶜ) = ∅) :
    Work.Whitney.doubleSet i =
      Work.Whitney.doubleSet f \ {(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} := by
  have h4disj : ∀ a b : M, (a, b) ∈ ({(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} : Set (M × M)) →
      (a = p₁ ∧ b = p₂) ∨ (a = p₂ ∧ b = p₁) ∨ (a = q₁ ∧ b = q₂) ∨ (a = q₂ ∧ b = q₁) := by
    intro a b h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] using h
  have h4mem : ∀ a b : M,
      ((a = p₁ ∧ b = p₂) ∨ (a = p₂ ∧ b = p₁) ∨ (a = q₁ ∧ b = q₂) ∨ (a = q₂ ∧ b = q₁)) →
      (a, b) ∈ ({(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} : Set (M × M)) := by
    intro a b h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] using h
  ext ⟨x, y⟩
  simp only [Work.Whitney.mem_doubleSet, Set.mem_sdiff]
  constructor
  · rintro ⟨hxy, hixy⟩
    by_cases hxW : x ∈ W₀
    · by_cases hyW : y ∈ W₀
      · exact absurd (hi_inj hxW hyW hixy) hxy
      · exfalso
        have hmem : i x ∈ (i '' W₀) ∩ (f '' W₀ᶜ) :=
          ⟨⟨x, hxW, rfl⟩, ⟨y, hyW, (hi_eq y hyW).symm.trans hixy.symm⟩⟩
        rw [hplace] at hmem
        exact hmem
    · by_cases hyW : y ∈ W₀
      · exfalso
        have hmem : i y ∈ (i '' W₀) ∩ (f '' W₀ᶜ) :=
          ⟨⟨y, hyW, rfl⟩, ⟨x, hxW, (hi_eq x hxW).symm.trans hixy⟩⟩
        rw [hplace] at hmem
        exact hmem
      · refine ⟨⟨hxy, ?_⟩, ?_⟩
        · rw [hi_eq x hxW, hi_eq y hyW] at hixy
          exact hixy
        · intro h4
          rcases h4disj x y h4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hyW (h2 ▸ hp₂W₀)
          · exact hxW (h1 ▸ hp₂W₀)
          · exact hyW (h2 ▸ hq₂W₀)
          · exact hxW (h1 ▸ hq₂W₀)
  · rintro ⟨⟨hxy, hfxy⟩, hnf⟩
    have hxW : x ∉ W₀ := by
      intro hxW
      have h4 : (x, y) ∈ ({(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} : Set (M × M)) := by
        by_cases hyW : y ∈ W
        · rcases hclean x y (hW₀sub hxW) hyW hfxy with h | h | h | h | h
          · exact absurd h hxy
          · exact h4mem x y (Or.inl h)
          · exact h4mem x y (Or.inr (Or.inl h))
          · exact h4mem x y (Or.inr (Or.inr (Or.inl h)))
          · exact h4mem x y (Or.inr (Or.inr (Or.inr h)))
        · exact absurd hfxy (hsep x y (hW₀sub hxW) hyW)
      exact hnf h4
    have hyW : y ∉ W₀ := by
      intro hyW
      have h4 : (x, y) ∈ ({(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} : Set (M × M)) := by
        by_cases hxW' : x ∈ W
        · rcases hclean x y hxW' (hW₀sub hyW) hfxy with h | h | h | h | h
          · exact absurd h hxy
          · exact h4mem x y (Or.inl h)
          · exact h4mem x y (Or.inr (Or.inl h))
          · exact h4mem x y (Or.inr (Or.inr (Or.inl h)))
          · exact h4mem x y (Or.inr (Or.inr (Or.inr h)))
        · exact absurd hfxy.symm (hsep y x (hW₀sub hyW) hxW')
      exact hnf h4
    refine ⟨hxy, ?_⟩
    rw [hi_eq x hxW, hi_eq y hyW]
    exact hfxy

theorem cancellation_of_pushData {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W)
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (W₀ : Set M) (O : Set (EuclideanSpace ℝ (Fin (2 * n))))
    (ψ σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hW₀open : IsOpen W₀) (hW₀sub : W₀ ⊆ W)
    (hp₂W₀ : p₂ ∈ W₀) (hq₂W₀ : q₂ ∈ W₀) (hp₁W₀ : p₁ ∉ W₀) (hq₁W₀ : q₁ ∉ W₀)
    (hOopen : IsOpen O) (hfront : f '' frontier W₀ ⊆ O) (hψid : ∀ y ∈ O, ψ y = y)
    (hψsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hσsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hleft : ∀ y, σ (ψ y) = y) (hright : ∀ y, ψ (σ y) = y)
    (hplace : ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ)
    (hfp₂ : f p₂ ∉ ψ '' (f '' W₀)) (hfq₂ : f q₂ ∉ ψ '' (f '' W₀)) :
    ∃ f' : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f' ∧
      (∀ y, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f' y)) ∧
      (∀ y : M, y ∉ W → f' y = f y) ∧
      Work.Whitney.doubleSet f' =
        Work.Whitney.doubleSet f \ {(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} ∧
      (∀ (u v : M), u ∉ W → v ∉ W →
        ∀ (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
          u ∈ c₁.source → v ∈ c₂.source →
          Work.Whitney.pairDet f' c₁ c₂ u v = Work.Whitney.pairDet f c₁ c₂ u v) := by
  classical
  have hinjψ : Function.Injective ψ := fun x y h => by
    have h2 := congrArg σ h
    rwa [hleft x, hleft y] at h2
  have hfj : Set.InjOn f W₀ := by
    intro x hx y hy hxy
    rcases hclean x y (hW₀sub hx) (hW₀sub hy) hxy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd (h1 ▸ hx) hp₁W₀
    · exact absurd (h2 ▸ hy) hp₁W₀
    · exact absurd (h1 ▸ hx) hq₁W₀
    · exact absurd (h2 ▸ hy) hq₁W₀
  let i : M → EuclideanSpace ℝ (Fin (2 * n)) := fun y => if y ∈ W₀ then ψ (f y) else f y
  have hiW : ∀ y ∈ W₀, i y = ψ (f y) := by intro y hy; simp only [i, if_pos hy]
  have hinW : ∀ y ∉ W₀, i y = f y := by intro y hy; simp only [i, if_neg hy]
  have hψne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hfcont : Continuous f := hf.continuous
  -- ## Smoothness of `i`.
  have hi_c : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) i := by
    intro y
    by_cases hy : y ∈ W₀
    · have hcomp : ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ψ (f z)) y :=
        (hψsm (f y)).comp y (hf y)
      exact hcomp.congr_of_eventuallyEq (by
        filter_upwards [hW₀open.mem_nhds hy] with z hz
        exact hiW z hz)
    · by_cases hyO : f y ∈ O
      · refine (hf y).congr_of_eventuallyEq ?_
        filter_upwards [(hfcont.continuousAt).preimage_mem_nhds (hOopen.mem_nhds hyO)] with z hz
        by_cases hzW : z ∈ W₀
        · rw [hiW z hzW, hψid (f z) hz]
        · rw [hinW z hzW]
      · have hcl : y ∉ closure W₀ := by
          intro h
          have h' : y ∈ interior W₀ ∪ frontier W₀ := by
            rw [← closure_eq_interior_union_frontier]; exact h
          rcases h' with h' | h'
          · rw [hW₀open.interior_eq] at h'; exact hy h'
          · exact hyO (hfront ⟨y, h', rfl⟩)
        refine (hf y).congr_of_eventuallyEq ?_
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hz
        exact hinW z (fun h => hz (subset_closure h))
  -- ## `i` is an immersion.
  have hi_imm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) i y) := by
    intro y
    by_cases hy : y ∈ W₀
    · have hev : i =ᶠ[𝓝 y] (fun z => ψ (f z)) := by
        filter_upwards [hW₀open.mem_nhds hy] with z hz
        rw [hiW z hz]
      rw [hev.mfderiv_eq]
      have hψd : MDifferentiableAt (𝓡 (2 * n)) (𝓡 (2 * n)) ψ (f y) :=
        (hψsm (f y)).mdifferentiableAt hψne
      have hfd : MDifferentiableAt (𝓡 n) (𝓡 (2 * n)) f y := (hf y).mdifferentiableAt hψne
      rw [show (fun z => ψ (f z)) = (ψ ∘ f) from rfl, mfderiv_comp y hψd hfd]
      intro a b hab
      exact himm y (injective_mfderiv_of_rightInverse hψsm hσsm hleft (f y) hab)
    · by_cases hyO : f y ∈ O
      · have hev : i =ᶠ[𝓝 y] f := by
          filter_upwards [(hfcont.continuousAt).preimage_mem_nhds (hOopen.mem_nhds hyO)] with z hz
          by_cases hzW : z ∈ W₀
          · rw [hiW z hzW, hψid (f z) hz]
          · rw [hinW z hzW]
        rw [hev.mfderiv_eq]
        exact himm y
      · have hcl : y ∉ closure W₀ := by
          intro h
          have h' : y ∈ interior W₀ ∪ frontier W₀ := by
            rw [← closure_eq_interior_union_frontier]; exact h
          rcases h' with h' | h'
          · rw [hW₀open.interior_eq] at h'; exact hy h'
          · exact hyO (hfront ⟨y, h', rfl⟩)
        have hev : i =ᶠ[𝓝 y] f := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hz
          exact hinW z (fun h => hz (subset_closure h))
        rw [hev.mfderiv_eq]
        exact himm y
  -- ## `i` is injective on the collar.
  have hi_inj : Set.InjOn i W₀ := by
    intro x hx y hy hxy
    rw [hiW x hx, hiW y hy] at hxy
    exact hfj hx hy (hinjψ hxy)
  -- ## The pushed image of the collar.
  have himg : i '' W₀ = ψ '' (f '' W₀) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, (hiW x hx).symm⟩
    · rintro ⟨w, ⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, hx, (hiW x hx).trans hz⟩
  -- ## The pushed sheet misses the image of the complement of the collar.
  have hplace' : (i '' W₀) ∩ (f '' W₀ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    rw [himg] at hz1
    obtain ⟨y, hy, hyz⟩ := hz2
    have hmem : z ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ := hplace hz1
    rcases hmem with ⟨x', hx', hx'z⟩ | hnot
    · have hx'y : f x' = f y := hx'z.trans hyz.symm
      by_cases hyW : y ∈ W
      · rcases hclean x' y (hW₀sub hx') hyW hx'y with h | h | h | h | h
        · exact hy (h ▸ hx')
        · exact hp₁W₀ (h.1 ▸ hx')
        · exact hfp₂ (by rw [← h.1, hx'z]; exact hz1)
        · exact hq₁W₀ (h.1 ▸ hx')
        · exact hfq₂ (by rw [← h.1, hx'z]; exact hz1)
      · exact hsep x' y (hW₀sub hx') hyW hx'y
    · exact hnot ⟨y, Set.mem_univ y, hyz⟩
  -- ## The double point set.
  have hds := doubleSet_of_push_aux f W p₁ p₂ q₁ q₂ hclean hsep W₀ i hW₀sub hp₂W₀ hq₂W₀
    hp₁W₀ hq₁W₀ hi_inj (fun y hy => hinW y hy) hplace'
  -- ## Agreement with `f` in a neighbourhood of every point outside `W`.
  have hagree : ∀ u : M, u ∉ W → i =ᶠ[𝓝 u] f := by
    intro u huW
    have huW₀ : u ∉ W₀ := fun h => huW (hW₀sub h)
    by_cases hucl : u ∈ closure W₀
    · have hufr : u ∈ frontier W₀ := by
        have h' : u ∈ interior W₀ ∪ frontier W₀ := by
          rw [← closure_eq_interior_union_frontier]; exact hucl
        rcases h' with h' | h'
        · rw [hW₀open.interior_eq] at h'; exact absurd h' huW₀
        · exact h'
      have hfuO : f u ∈ O := hfront ⟨u, hufr, rfl⟩
      filter_upwards [(hfcont.continuousAt).preimage_mem_nhds (hOopen.mem_nhds hfuO)] with x hx
      by_cases hxW : x ∈ W₀
      · rw [hiW x hxW, hψid (f x) hx]
      · rw [hinW x hxW]
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hucl] with x hx
      exact hinW x (fun h => hx (subset_closure h))
  refine ⟨i, hi_c, hi_imm, ?_, hds, ?_⟩
  · intro y hy
    exact hinW y (fun h => hy (hW₀sub h))
  · intro u v huW hvW c₁ c₂ hu₁ hv₂
    exact (pairDet_congr c₁ c₂ u v hu₁ hv₂ (hagree u huW).symm (hagree v hvW).symm).symm

end Work.Whitney
