import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.SeedExist.Pairs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedExist.Sides

open Classical Filter Function Set
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-!
# `Work.SeedExist.Sides.cycle_mem_Snear`

The other points `T_c^j z₁` (`j = 1, …, 4`) of the parabolic cycle lie on the **near side**
`Snear` of the level-`0` α-pair, the side through the long complementary arc from `α₂` to `α₁`.

The proof: for `1 ≤ j ≤ 4`, the ray of angle `T^j α₁` lands at `T_c^j z₁` (the portrait
propagates along the orbit, `Work.ELTop.landsN_map`), and the angle `T^j α₁` lies in the near
arc `(α₂, α₁ + 1)`.  Every ray point of a ray whose angle lies in the near arc lies in the near
side (the explicit path argument `rayPt_mem_sideThrough_of_InArc`).  Hence `T_c^j z₁`, being the
limit of those ray points, lies in the closure of `Snear`; and since it lies in the filled Julia
set `K c` while the pair curve meets `K c` only at `z₁ ≠ T_c^j z₁`, it is off the pair curve.
The complement of the pair curve is an open set, `Snear` is one of its components, and the
closed ray `R(T^j α₁) ∪ {T_c^j z₁}` together with `Snear` is a preconnected subset of the
complement containing the reference point of `Snear`; maximality of the component therefore
places `T_c^j z₁` in `Snear`.
-/

/-! ## The base pair of the level-`0` α-pair -/

/-- The (literally written) base pair `{α₁, α₂}` with landing point `z₁`; it is
`Work.EL.alphaPairRaw c z₁ 0` up to the evaluation of `min`/`max`. -/
private abbrev Q0 (z₁ : ℂ) : Work.EL.RawPair :=
  ⟨Work.EL.alpha1, Work.EL.alpha2, z₁⟩

/-- `Snear` is the near side of the base pair: the component of the complement of the pair curve
through `Q0` which contains the ray point at the middle of the complementary arc. -/
private theorem sideThrough_Q0_eq_Snear {c : ℂ} {z₁ : ℂ}
    (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) :
    Work.EL.RawPair.sideThrough hN (Q0 z₁) Work.EL.alpha2 Work.EL.alpha1 =
      Work.SeedExist.Snear hN z₁ := by
  have hle : Work.EL.alpha1 ≤ Work.EL.alpha2 := by norm_num [Work.EL.alpha1, Work.EL.alpha2]
  unfold Work.SeedExist.Snear Work.SeedExist.alphaPair
  rw [Work.SeedExist.wakeHi_zero, Work.SeedExist.wakeLo_zero]
  simp only [Work.EL.alphaPairRaw, Function.iterate_zero_apply,
    min_eq_left hle, max_eq_right hle]

/-! ## Angle arithmetic -/

/-- `arcLen` does not change when the second endpoint is shifted by `1`. -/
private theorem arcLen_add_one_at (u v : ℝ) : Work.EL.arcLen u (v + 1) = Work.EL.arcLen u v := by
  have h : v + 1 - u = (v - u) + 1 := by ring
  rw [Work.EL.arcLen, Work.EL.arcLen, h, Int.fract_add_one]

/-- The membership in the pair curve of a raw pair, in the right-associated form used by
`rcases`. -/
private theorem mem_curve_iff {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.RawPair) (z : ℂ) :
    z ∈ Work.EL.RawPair.curve hN P ↔
      z ∈ Work.EL.paramRay hN P.a ∨ z = P.y ∨ z ∈ Work.EL.paramRay hN P.b := by
  simp only [Work.EL.RawPair.curve, Set.mem_union, Set.mem_singleton_iff]
  tauto

/-! ## A ray point in the near arc lies in the near side -/

/-- **The path argument, for a raw pair**: a ray point of angle `θ ∈ (P.b, P.a + 1)` (the open
near arc of a pair with `P.a < P.b < P.a + 1`) at a level `t > 1` lies in the side
`sideThrough hN P P.b P.a`.

The explicit path consists of the piece of the ray of angle `θ` between the levels `2` and `t`
and the equipotential arc of level `2` between the near-arc midpoint and `θ`; both pieces are
continuous images of intervals, hence preconnected, and both avoid the pair curve because the
relevant angles are congruent modulo `ℤ` to neither `P.a` nor `P.b` and because the landing
point `P.y` lies in the filled Julia set, where the ray points do not. -/
private theorem rayPt_mem_sideThrough_of_Ioo {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.RawPair) (hab : P.a < P.b) (hyK : P.y ∈ Work.EL.K c)
    {θ t : ℝ} (hθ1 : P.b < θ) (hθ2 : θ < P.a + 1) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.RawPair.sideThrough hN P P.b P.a := by
  have hθ : θ ∈ Set.Ioo P.b (P.a + 1) := ⟨hθ1, hθ2⟩
  have hb1 : P.b < P.a + 1 := lt_trans hθ1 hθ2
  set mid : ℝ := P.b + Work.EL.arcLen P.b P.a / 2 with hmid_def
  have hmid_mem : mid ∈ Set.Ioo P.b (P.a + 1) := Work.ELTop.mid_mem_nearArc hab hb1
  -- the two pieces of the path
  set S : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t
      ∪ (fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc mid θ with hS_def
  have hcont1 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN θ s) (Set.uIcc (2 : ℝ) t) :=
    (Work.Top.continuousOn_rayPt hN θ).mono (fun s hs => by
      rw [Set.mem_Ioi]
      rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
      · linarith
      · linarith)
  have hcont2 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN s 2) (Set.uIcc mid θ) :=
    (Work.ELTop.continuous_rayPt_angle hN (R := 2) (by norm_num)).continuousOn
  have hpre1 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t) :=
    (isPreconnected_uIcc (a := (2 : ℝ)) (b := t)).image _ hcont1
  have hpre2 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc mid θ) :=
    (isPreconnected_uIcc (a := mid) (b := θ)).image _ hcont2
  have hpre : IsPreconnected S := by
    rw [hS_def]
    exact IsPreconnected.union (Work.EL.rayPt hN θ 2)
      ⟨2, Set.left_mem_uIcc, rfl⟩ ⟨θ, Set.right_mem_uIcc, rfl⟩ hpre1 hpre2
  -- the path avoids the pair curve
  have hS_sub : S ⊆ (Work.EL.RawPair.curve hN P)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, mem_curve_iff hN P z]
    simp only [not_or]
    rw [hS_def] at hz
    rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · have hs1 : 1 < s := by
        rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
        · linarith
        · linarith
      obtain ⟨hθA, hθB⟩ := Work.ELTop.nearArc_ne_add_int hab hθ
      refine ⟨Work.ELTop.notMem_paramRay_of_ne_int hN hθA hs1, ?_,
        Work.ELTop.notMem_paramRay_of_ne_int hN hθB hs1⟩
      intro hzy
      have hzK : P.y ∈ Work.EL.K c := hyK
      rw [← hzy] at hzK
      exact (Work.EL.paramRay_subset_compl hN θ (Work.EL.rayPt_mem_paramRay hN hs1)) hzK
    · have hs_mem : s ∈ Set.Ioo P.b (P.a + 1) := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨hmid_mem.1.trans_le h1, h2.trans_lt hθ.2⟩
        · exact ⟨hθ.1.trans_le h1, h2.trans_lt hmid_mem.2⟩
      obtain ⟨hsA, hsB⟩ := Work.ELTop.nearArc_ne_add_int hab hs_mem
      refine ⟨Work.ELTop.notMem_paramRay_of_ne_int hN hsA (by norm_num), ?_,
        Work.ELTop.notMem_paramRay_of_ne_int hN hsB (by norm_num)⟩
      intro hzy
      have hzK : P.y ∈ Work.EL.K c := hyK
      rw [← hzy] at hzK
      exact (Work.EL.paramRay_subset_compl hN s
        (Work.EL.rayPt_mem_paramRay hN (by norm_num : (1 : ℝ) < 2))) hzK
  -- the reference point and the target point lie on the path
  have hx_mem : Work.EL.rayPt hN mid 2 ∈ S := by
    rw [hS_def]
    exact Or.inr ⟨mid, Set.left_mem_uIcc, rfl⟩
  have hyt_mem : Work.EL.rayPt hN θ t ∈ S := by
    rw [hS_def]
    exact Or.inl ⟨t, Set.right_mem_uIcc, rfl⟩
  have hmem : Work.EL.rayPt hN θ t ∈
      connectedComponentIn (Work.EL.RawPair.curve hN P)ᶜ (Work.EL.rayPt hN mid 2) :=
    IsPreconnected.subset_connectedComponentIn hpre hx_mem hS_sub hyt_mem
  show Work.EL.rayPt hN θ t ∈ connectedComponentIn (Work.EL.RawPair.curve hN P)ᶜ
    (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2)
  exact hmem

/-- **The path argument, with the angle normalized**: a ray point of angle `θ` lying in the
cyclic near arc of the pair `P` lies in the near side `sideThrough hN P P.b P.a`.  The angle is
replaced by its `Int.fract` representative in `(P.b, P.a + 1)`; ray points are `1`-periodic in
the angle. -/
private theorem rayPt_mem_sideThrough_of_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.RawPair) (hab : P.a < P.b) (hb1 : P.b < P.a + 1)
    (hyK : P.y ∈ Work.EL.K c) {θ t : ℝ}
    (hθ : Work.EL.InArc θ P.b (P.a + 1)) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.RawPair.sideThrough hN P P.b P.a := by
  set k : ℤ := ⌊θ - P.b⌋ with hk
  set θ₀ : ℝ := θ - (k : ℝ) with hθ₀
  have hfract : θ₀ - P.b = Int.fract (θ - P.b) := by
    have h := Int.floor_add_fract (θ - P.b)
    rw [← hk] at h
    rw [hθ₀]
    linarith
  have harcP : Work.EL.arcLen P.b P.a = P.a - P.b + 1 := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  have harc1 : Work.EL.arcLen P.b (P.a + 1) = Work.EL.arcLen P.b P.a :=
    arcLen_add_one_at P.b P.a
  have hθ₀1 : P.b < θ₀ := by linarith [hfract, hθ.1]
  have hθ₀2 : θ₀ < P.a + 1 := by
    have h2 : θ₀ - P.b < Work.EL.arcLen P.b (P.a + 1) := by rw [hfract]; exact hθ.2
    rw [harc1, harcP] at h2
    linarith
  have hmain := rayPt_mem_sideThrough_of_Ioo hN P hab hyK hθ₀1 hθ₀2 ht
  have hperiod : Work.EL.rayPt hN θ t = Work.EL.rayPt hN θ₀ t := by
    have h1 : θ = θ₀ + (k : ℝ) := by rw [hθ₀]; ring
    rw [h1, Work.ELTop.rayPt_add_int hN θ₀ t k]
  rwa [hperiod]

/-! ## The main theorem -/

theorem cycle_mem_Snear {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hJ : Work.Top.JordanForm) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (hg : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hex : ∀ j : ℕ, 0 < j → j < 5 → (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ≠ z₁)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 4) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ∈ Work.SeedExist.Snear hN z₁ := by
  classical
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  have L1 : Work.EL.LandsN hN Work.EL.alpha1 z₁ :=
    (Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha1 z₁).mpr h1
  have hzK : z₁ ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN L1
  -- the portrait propagates along the orbit: the ray of angle `T^n α₁` lands at `T_c^n z₁`
  have hland : ∀ n : ℕ,
      Work.EL.LandsN hN ((Work.EL.T^[n]) Work.EL.alpha1) ((Tantibar c)^[n] z₁) := by
    intro n
    induction n with
    | zero => simpa using L1
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Work.ELTop.landsN_map hN hφ ih
  have hL : Work.EL.LandsN hN ((Work.EL.T^[j]) Work.EL.alpha1)
      ((Tantibar c)^[j] z₁) := hland j
  -- the angle of the iterated ray lies in the near arc `(α₂, α₁ + 1)`
  have hInArc : Work.EL.InArc ((Work.EL.T^[j]) Work.EL.alpha1) Work.EL.alpha2
      (Work.EL.alpha1 + 1) := by
    interval_cases j <;>
      norm_num [Work.EL.InArc, Work.EL.arcLen, Work.EL.alpha1, Work.EL.alpha2, Work.EL.T,
        Int.fract, Function.iterate_succ_apply', Function.iterate_zero]
  have hSide := sideThrough_Q0_eq_Snear (z₁ := z₁) hN
  have hab : (Q0 z₁).a < (Q0 z₁).b := by
    show Work.EL.alpha1 < Work.EL.alpha2
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hb1 : (Q0 z₁).b < (Q0 z₁).a + 1 := by
    show Work.EL.alpha2 < Work.EL.alpha1 + 1
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hyK : (Q0 z₁).y ∈ Work.EL.K c := hzK
  -- every ray point of the iterated ray lies in the base pair's near side
  have hside_t : ∀ t : ℝ, 1 < t →
      Work.EL.rayPt hN ((Work.EL.T^[j]) Work.EL.alpha1) t ∈
        Work.EL.RawPair.sideThrough hN (Q0 z₁) Work.EL.alpha2 Work.EL.alpha1 :=
    fun t ht => rayPt_mem_sideThrough_of_InArc hN (Q0 z₁) hab hb1 hyK hInArc ht
  have hray_sub : Work.EL.paramRay hN ((Work.EL.T^[j]) Work.EL.alpha1) ⊆
      Work.EL.RawPair.sideThrough hN (Q0 z₁) Work.EL.alpha2 Work.EL.alpha1 := by
    intro z hz
    obtain ⟨hzc, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
    have hzt : z = Work.EL.rayPt hN ((Work.EL.T^[j]) Work.EL.alpha1) t :=
      Work.Top.NakaneData.injOn_Phi hN hzc (Work.Top.NakaneData.rayPt_notMem hN ht)
        (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
    rw [hzt]
    exact hside_t t ht
  -- the landing point is the limit of those ray points, so it lies in the closure of the side
  have hy_cl : (Tantibar c)^[j] z₁ ∈
      closure (Work.EL.paramRay hN ((Work.EL.T^[j]) Work.EL.alpha1)) :=
    mem_closure_of_tendsto hL (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Work.EL.rayPt_mem_paramRay hN ht)
  -- the landing point is not the parabolic point, and it is off the pair curve
  have hyne : (Tantibar c)^[j] z₁ ≠ z₁ := hex j (by omega) (by omega)
  have hyK' : (Tantibar c)^[j] z₁ ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN hL
  have hy_notmem : (Tantibar c)^[j] z₁ ∉ Work.EL.RawPair.curve hN (Q0 z₁) := by
    rw [mem_curve_iff hN (Q0 z₁) ((Tantibar c)^[j] z₁)]
    rintro (h | h | h)
    · exact (Work.EL.paramRay_subset_compl hN Work.EL.alpha1 h) hyK'
    · exact hyne h
    · exact (Work.EL.paramRay_subset_compl hN Work.EL.alpha2 h) hyK'
  -- the closed ray `R(T^j α₁) ∪ {T^j z₁}` is preconnected
  have hTpre : IsPreconnected (Work.EL.paramRay hN ((Work.EL.T^[j]) Work.EL.alpha1) ∪
      {(Tantibar c)^[j] z₁}) :=
    (Work.ELTop.isPreconnected_paramRay hN _).subset_closure Set.subset_union_left
      (Set.union_subset subset_closure (by rw [Set.singleton_subset_iff]; exact hy_cl))
  -- the union with the side is preconnected and contained in the complement
  have hx0 : Work.EL.rayPt hN ((Work.EL.T^[j]) Work.EL.alpha1) 2 ∈
      Work.SeedExist.Snear hN z₁ := by
    rw [← hSide]
    exact hside_t 2 (by norm_num)
  have hSpre : IsPreconnected (Work.SeedExist.Snear hN z₁ ∪
      (Work.EL.paramRay hN ((Work.EL.T^[j]) Work.EL.alpha1) ∪ {(Tantibar c)^[j] z₁})) := by
    refine IsPreconnected.union _ hx0
      (Or.inl (Work.EL.rayPt_mem_paramRay hN (by norm_num))) ?_ hTpre
    rw [← hSide]
    exact isPreconnected_connectedComponentIn
  have hsub : Work.SeedExist.Snear hN z₁ ∪
      (Work.EL.paramRay hN ((Work.EL.T^[j]) Work.EL.alpha1) ∪ {(Tantibar c)^[j] z₁}) ⊆
      (Work.EL.RawPair.curve hN (Q0 z₁))ᶜ := by
    rintro z (hzs | hzr | hzy)
    · rw [← hSide] at hzs
      exact connectedComponentIn_subset _ _ hzs
    · exact connectedComponentIn_subset _ _ (hray_sub hzr)
    · rw [Set.mem_singleton_iff] at hzy
      rw [hzy]
      exact hy_notmem
  have hmax : Work.SeedExist.Snear hN z₁ ∪
      (Work.EL.paramRay hN ((Work.EL.T^[j]) Work.EL.alpha1) ∪ {(Tantibar c)^[j] z₁}) ⊆
      connectedComponentIn ((Work.EL.RawPair.curve hN (Q0 z₁))ᶜ)
        (Work.EL.rayPt hN ((Work.EL.T^[j]) Work.EL.alpha1) 2) :=
    IsPreconnected.subset_connectedComponentIn hSpre (Or.inl hx0) hsub
  -- the component of the complement containing `x₀` is `Snear`
  have hcc : connectedComponentIn ((Work.EL.RawPair.curve hN (Q0 z₁))ᶜ)
      (Work.EL.rayPt hN ((Work.EL.T^[j]) Work.EL.alpha1) 2) = Work.SeedExist.Snear hN z₁ := by
    have hx0s : Work.EL.rayPt hN ((Work.EL.T^[j]) Work.EL.alpha1) 2 ∈
        Work.EL.RawPair.sideThrough hN (Q0 z₁) Work.EL.alpha2 Work.EL.alpha1 := by
      rw [hSide]
      exact hx0
    have hx0c : Work.EL.rayPt hN ((Work.EL.T^[j]) Work.EL.alpha1) 2 ∈
        connectedComponentIn ((Work.EL.RawPair.curve hN (Q0 z₁))ᶜ)
          (Work.EL.rayPt hN (Work.EL.alpha2 + Work.EL.arcLen Work.EL.alpha2 Work.EL.alpha1 / 2)
            2) := hx0s
    rw [← connectedComponentIn_eq hx0c]
    exact hSide
  exact hcc ▸ hmax (Or.inr (Or.inr (Set.mem_singleton _)))

end

end Work.SeedExist.Sides
