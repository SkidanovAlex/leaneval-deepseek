import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.concat_conj
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.homotopic_cast_of_trans_const
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.homotopic_of_isSimplyConnected_of_range_subset
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.homotopic_refl_of_trans_conj
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.pathConnectedSpace_of_cover

/-!
# Van Kampen for a cover by two simply connected open sets

If `U` and `V` are open subsets of a topological space `X`, both simply connected, and `U ∩ V` is
path connected, then `U ∪ V` is simply connected.

The proof is the standard one: subdivide a loop into finitely many pieces, each lying in `U` or in
`V` (Lebesgue number for the open cover `{γ ⁻¹' U, γ ⁻¹' V}` of the unit interval); conjugate each
piece by paths lying in `U ∩ V`, so that each conjugated piece is a loop lying inside `U` or inside
`V`, hence null-homotopic; a telescoping identity then produces a null-homotopy of the loop.
-/

namespace Work.SimplyConnected.ABS

theorem loop_homotopic_refl_of_isSimplyConnected {Z : Type*} [TopologicalSpace Z] {s : Set Z}
    (hs : IsSimplyConnected s) {x : Z} (γ : Path x x) (hγ : ∀ t, γ t ∈ s) :
    Path.Homotopic γ (Path.refl x) := by
  obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hs).2 x γ hγ
  exact ⟨F⟩

theorem Path.trans_mem {Z : Type*} [TopologicalSpace Z] {s : Set Z} {a b c : Z}
    (p : Path a b) (q : Path b c) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    ∀ t, (p.trans q) t ∈ s := by
  intro t
  rw [Path.trans_apply]
  split_ifs with h
  · exact hp _
  · exact hq _

theorem Path.symm_mem {Z : Type*} [TopologicalSpace Z] {s : Set Z} {a b : Z}
    (p : Path a b) (hp : ∀ t, p t ∈ s) : ∀ t, p.symm t ∈ s := by
  intro t
  simpa using hp (unitInterval.symm t)

theorem isPathConnected_inter_of {Z : Type*} [TopologicalSpace Z] {A B X Y : Set Z}
    (hX : X = A ∨ X = B) (hY : Y = A ∨ Y = B ∨ Y = Set.univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hI : IsPathConnected (A ∩ B)) :
    IsPathConnected (X ∩ Y) := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · simpa using hA
  · exact hI
  · simpa using hA
  · rw [Set.inter_comm]; exact hI
  · simpa using hB
  · simpa using hB

theorem pathConnectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hX : PathConnectedSpace X) : PathConnectedSpace Y where
  nonempty := hX.nonempty.map e
  joined y₁ y₂ := by
    obtain ⟨p⟩ := hX.joined (e.symm y₁) (e.symm y₂)
    exact ⟨(p.map e.continuous).cast (e.apply_symm_apply y₁).symm (e.apply_symm_apply y₂).symm⟩

def homeomorphSubtypePreimage {X : Type*} [TopologicalSpace X] {W s : Set X} (h : s ⊆ W) :
    ↥(Subtype.val ⁻¹' s : Set ↥W) ≃ₜ ↥s where
  toFun y := ⟨(y.1 : X), y.2⟩
  invFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  left_inv y := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
    (fun y => y.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun x => h x.2)) (fun x => x.2)

theorem simplyConnectedSpace_preimage_subtype_val {X : Type*} [TopologicalSpace X] {W s : Set X}
    (h : s ⊆ W) (hs : SimplyConnectedSpace ↥s) :
    SimplyConnectedSpace ↥(Subtype.val ⁻¹' s : Set ↥W) := by
  exact ContinuousMap.HomotopyEquiv.simplyConnectedSpace (hY := hs)
    (homeomorphSubtypePreimage h).toHomotopyEquiv

theorem pathConnectedSpace_preimage_subtype_val {X : Type*} [TopologicalSpace X] {W s : Set X}
    (h : s ⊆ W) (hs : PathConnectedSpace ↥s) :
    PathConnectedSpace ↥(Subtype.val ⁻¹' s : Set ↥W) :=
  pathConnectedSpace_of_homeomorph (homeomorphSubtypePreimage (W := W) (s := s) h).symm hs

theorem exists_partition_nat {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAo : IsOpen A) (hBo : IsOpen B) (hAB : A ∪ B = Set.univ) {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (t : ℕ → ↥unitInterval) (S : ℕ → Set X),
      0 < n ∧ t 0 = 0 ∧ t n = 1 ∧ Monotone t ∧
      (∀ k, k < n → S k = A ∨ S k = B) ∧
      (∀ k, n ≤ k → S k = Set.univ) ∧
      (∀ k, k < n → Set.Icc (t k) (t (k + 1)) ⊆ γ ⁻¹' S k) := by
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, hpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (ι := Bool)
      (c := fun b => γ ⁻¹' (if b then B else A))
      (fun b => γ.continuous.isOpen_preimage _ (by cases b <;> assumption))
      (by
        intro z hz
        rw [Set.mem_iUnion]
        rcases (show γ z ∈ A ∪ B from by rw [hAB]; exact Set.mem_univ _) with h | h
        · exact ⟨false, by simpa using h⟩
        · exact ⟨true, by simpa using h⟩)
  have hNpos : 0 < N := by
    by_contra h
    have h0 : t 0 = 1 := hN 0 (by omega)
    rw [ht0] at h0
    have : ((0 : ↥unitInterval) : ℝ) = 1 := congrArg Subtype.val h0
    norm_num at this
  let S : ℕ → Set X :=
    fun k => if h : k < N then (if (hpiece k).choose then B else A) else Set.univ
  have hS1 : ∀ k, k < N → S k = A ∨ S k = B := by
    intro k hk
    dsimp only [S]
    rw [dif_pos hk]
    cases hc : (hpiece k).choose
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hS2 : ∀ k, N ≤ k → S k = Set.univ := by
    intro k hk
    dsimp only [S]
    exact dif_neg (by omega)
  have hS3 : ∀ k, k < N → Set.Icc (t k) (t (k + 1)) ⊆ γ ⁻¹' S k := by
    intro k hk
    dsimp only [S]
    rw [dif_pos hk]
    exact (hpiece k).choose_spec
  exact ⟨N, t, S, hNpos, ht0, hN N le_rfl, htmono, hS1, hS2, hS3⟩

theorem loop_nullhomotopic {Z : Type*} [TopologicalSpace Z] {A B : Set Z}
    (hAo : IsOpen A) (hBo : IsOpen B) (hAB : A ∪ B = Set.univ)
    (hA : IsSimplyConnected A) (hB : IsSimplyConnected B) (hI : IsPathConnected (A ∩ B))
    (p₀ : Z) (hp₀ : p₀ ∈ A ∩ B) (γ : Path p₀ p₀) :
    Path.Homotopic γ (Path.refl p₀) := by
  obtain ⟨n, t, S, hn, ht0, htn, htmono, hSAB, hSuniv, hSsub⟩ :=
    exists_partition_nat hAo hBo hAB γ
  let T : ℕ → Set Z := fun k => if h : k < n then S k else Set.univ
  have hTpiece : ∀ k, k < n → T k = A ∨ T k = B := by
    intro k hk
    dsimp only [T]
    rw [dif_pos hk]
    exact hSAB k hk
  have hTuniv : ∀ k, n ≤ k → T k = Set.univ := by
    intro k hk
    dsimp only [T]
    exact dif_neg (by omega)
  have hTmem : ∀ k, T k = A ∨ T k = B ∨ T k = Set.univ := by
    intro k
    by_cases hk : k < n
    · rcases hTpiece k hk with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hTuniv k (by omega)))
  let tF : Fin (n + 1) → ↥unitInterval := fun i => t i.val
  let xs : Fin (n + 1) → Z := fun i => γ (t i.val)
  let cs : (k : Fin n) → Path (xs k.castSucc) (xs k.succ) :=
    fun k => γ.subpath (t k.val) (t (k.val + 1))
  let C : Path (xs 0) (xs (Fin.last n)) := Path.concat xs cs
  have hxs0 : xs 0 = p₀ := by
    dsimp only [xs]
    rw [show ((0 : Fin (n + 1)).val) = 0 from rfl, ht0]
    exact γ.source
  have hxsn : xs (Fin.last n) = p₀ := by
    dsimp only [xs]
    rw [Fin.val_last, htn]
    exact γ.target
  have hl : xs 0 = xs (Fin.last n) := hxs0.trans hxsn.symm
  have hxsT : ∀ i : Fin (n + 1), xs i ∈ T i.val := by
    intro i
    by_cases hi : i.val < n
    · dsimp only [xs, T]
      rw [dif_pos hi]
      exact hSsub i.val hi ⟨le_rfl, htmono (Nat.le_succ _)⟩
    · dsimp only [T]
      rw [dif_neg hi]
      exact Set.mem_univ _
  have hxsTim1 : ∀ i : Fin (n + 1), xs i ∈ T (i.val - 1) := by
    intro i
    have hi : i.val - 1 < n := by omega
    dsimp only [xs, T]
    rw [dif_pos hi]
    exact hSsub (i.val - 1) hi ⟨htmono (by omega), htmono (by omega)⟩
  have hxs0A : xs 0 ∈ A := hxs0 ▸ hp₀.1
  have hxs0B : xs 0 ∈ B := hxs0 ▸ hp₀.2
  have hTmem0 : ∀ k, xs 0 ∈ T k := by
    intro k
    by_cases hk : k < n
    · dsimp only [T]
      rw [dif_pos hk]
      rcases hSAB k hk with h | h
      · rw [h]; exact hxs0A
      · rw [h]; exact hxs0B
    · dsimp only [T]
      rw [dif_neg hk]
      exact Set.mem_univ _
  have hApc : IsPathConnected A := IsSimplyConnected.isPathConnected hA
  have hBpc : IsPathConnected B := IsSimplyConnected.isPathConnected hB
  have hIpc : IsPathConnected (A ∩ B) := hI
  have hMpc : ∀ i : Fin (n + 1), IsPathConnected (T (i.val - 1) ∩ T i.val) := by
    intro i
    exact isPathConnected_inter_of (hTpiece (i.val - 1) (by omega)) (hTmem i.val)
      hApc hBpc hIpc
  have hgs_exists : ∀ i : Fin (n + 1),
      ∃ g : Path (xs 0) (xs i), ∀ u, g u ∈ T (i.val - 1) ∩ T i.val :=
    fun i => (hMpc i).joinedIn (xs 0) ⟨hTmem0 _, hTmem0 _⟩ (xs i) ⟨hxsTim1 i, hxsT i⟩
  let gs : (i : Fin (n + 1)) → Path (xs 0) (xs i) := fun i => Classical.choose (hgs_exists i)
  have hgs_mem : ∀ (i : Fin (n + 1)) (u : ↥unitInterval),
      gs i u ∈ T (i.val - 1) ∩ T i.val := fun i => Classical.choose_spec (hgs_exists i)
  have hcs_mem : ∀ (k : Fin n) (u : ↥unitInterval), cs k u ∈ S k.val := by
    intro k u
    dsimp only [cs]
    have hmem : (γ.subpath (t k.val) (t (k.val + 1))) u ∈
        Set.range (γ.subpath (t k.val) (t (k.val + 1))) := ⟨u, rfl⟩
    rw [Path.range_subpath] at hmem
    rw [Set.uIcc_of_le (htmono (Nat.le_succ _))] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    rw [← hvu]
    exact hSsub k.val k.isLt hv
  have hM1 : ∀ k : Fin n, ∀ z ∈ T (k.val - 1) ∩ T k.val, z ∈ S k.val := by
    intro k z hz
    have h : z ∈ T k.val := hz.2
    dsimp only [T] at h
    rw [dif_pos k.isLt] at h
    exact h
  have hM2 : ∀ k : Fin n, ∀ z ∈ T ((k.succ).val - 1) ∩ T (k.succ).val, z ∈ S k.val := by
    intro k z hz
    have h2 : z ∈ T ((k.succ).val - 1) := hz.1
    have hval : (k.succ).val - 1 = k.val := by rw [Fin.val_succ]; omega
    have h : z ∈ T k.val := by rwa [hval] at h2
    dsimp only [T] at h
    rw [dif_pos k.isLt] at h
    exact h
  let r : (k : Fin n) → Path (xs 0) (xs 0) :=
    fun k => (gs k.castSucc).trans ((cs k).trans (gs k.succ).symm)
  have hr_mem : ∀ (k : Fin n) (u : ↥unitInterval), r k u ∈ S k.val := by
    intro k u
    dsimp only [r]
    exact Path.trans_mem (gs k.castSucc) ((cs k).trans (gs k.succ).symm)
      (fun v => hM1 k _ (hgs_mem (k.castSucc) v))
      (Path.trans_mem (cs k) (gs k.succ).symm (fun v => hcs_mem k v)
        (Path.symm_mem (gs k.succ) (fun v => hM2 k _ (hgs_mem (k.succ) v)))) u
  have hnull : ∀ k : Fin n, Path.Homotopic (r k) (Path.refl (xs 0)) := by
    intro k
    rcases hSAB k.val k.isLt with h | h
    · exact loop_homotopic_refl_of_isSimplyConnected (by rw [h]; exact hA) (r k) (hr_mem k)
    · exact loop_homotopic_refl_of_isSimplyConnected (by rw [h]; exact hB) (r k) (hr_mem k)
  have hconc : Path.Homotopic (Path.concat (fun _ : Fin (n + 1) => xs 0) r)
      (Path.refl (xs 0)) :=
    (Path.Homotopic.concat_hcomp (fun _ : Fin (n + 1) => xs 0) r
      (fun _ => Path.refl (xs 0)) hnull).trans
      (by rw [Path.concat_refl n (xs 0)])
  have htel := concat_conj n (xs 0) xs gs cs
  have h1 : Path.Homotopic ((gs 0).trans (C.trans (gs (Fin.last n)).symm))
      (Path.refl (xs 0)) := htel.symm.trans hconc
  have hs0 : Path.Homotopic (gs 0) (Path.refl (xs 0)) := by
    have hm : ∀ u, gs 0 u ∈ T 0 := fun u => (hgs_mem 0 u).2
    rcases hTpiece 0 hn with h | h
    · exact loop_homotopic_refl_of_isSimplyConnected (s := T 0) (by rw [h]; exact hA) (gs 0) hm
    · exact loop_homotopic_refl_of_isSimplyConnected (s := T 0) (by rw [h]; exact hB) (gs 0) hm
  let costN : Path (xs 0) (xs (Fin.last n)) :=
    Path.cast (Path.refl (xs (Fin.last n))) hl rfl
  have hsn : Path.Homotopic (gs (Fin.last n)) costN := by
    have hlast : T ((Fin.last n).val - 1) = A ∨ T ((Fin.last n).val - 1) = B :=
      hTpiece _ (by rw [Fin.val_last]; omega)
    have hmem1 : ∀ u, gs (Fin.last n) u ∈ T ((Fin.last n).val - 1) :=
      fun u => (hgs_mem (Fin.last n) u).1
    have hmem2 : ∀ u, costN u ∈ T ((Fin.last n).val - 1) := by
      intro u
      have hcu : costN u = xs (Fin.last n) := by simp [costN, Path.cast_coe]
      rw [hcu]
      exact hxsTim1 (Fin.last n)
    rcases hlast with h | h
    · exact homotopic_of_isSimplyConnected_of_range_subset (by rw [h]; exact hA)
        (hTmem0 _) (hxsTim1 _) (gs (Fin.last n)) costN hmem1 hmem2
    · exact homotopic_of_isSimplyConnected_of_range_subset (by rw [h]; exact hB)
        (hTmem0 _) (hxsTim1 _) (gs (Fin.last n)) costN hmem1 hmem2
  have h2 : Path.Homotopic (C.trans costN.symm) (Path.refl (xs 0)) := by
    have hstep : Path.Homotopic ((Path.refl (xs 0)).trans (C.trans costN.symm))
        ((gs 0).trans (C.trans (gs (Fin.last n)).symm)) :=
      Path.Homotopic.hcomp hs0.symm
        (Path.Homotopic.hcomp (Path.Homotopic.refl C) (Path.Homotopic.symm₂ hsn.symm))
    exact (Path.Homotopic.refl_trans (C.trans costN.symm)).symm.trans (hstep.trans h1)
  have h3 : Path.Homotopic (Path.cast C rfl hl) (Path.refl (xs 0)) :=
    homotopic_cast_of_trans_const hl C h2
  have hφc : Continuous (Set.Icc.convexComb (tF 0) (tF (Fin.last n))) :=
    Set.Icc.continuous_convexComb _ _
  have hφ0 : Set.Icc.convexComb (tF 0) (tF (Fin.last n)) 0 = 0 := by
    rw [Set.Icc.convexComb_zero]
    exact ht0
  have hφ1 : Set.Icc.convexComb (tF 0) (tF (Fin.last n)) 1 = 1 := by
    rw [Set.Icc.convexComb_one]
    exact htn
  have e0 : p₀ = xs 0 := hxs0.symm
  have eN : p₀ = xs (Fin.last n) := hxsn.symm
  have hpath : Path.Homotopic (Path.cast C e0 eN) γ := by
    have h1' := Path.Homotopic.pathCast (Path.Homotopic.concat_subpath γ tF) e0 eN
    have hcast : (γ.subpath (tF 0) (tF (Fin.last n))).cast e0 eN =
        γ.reparam (Set.Icc.convexComb (tF 0) (tF (Fin.last n))) hφc hφ0 hφ1 := by
      apply Path.ext
      rfl
    rw [hcast] at h1'
    exact h1'.trans ⟨(Path.Homotopy.reparam γ _ hφc hφ0 hφ1).symm⟩
  have h4 : Path.Homotopic (Path.cast C e0 eN) (Path.refl p₀) := by
    have h := Path.Homotopic.pathCast h3 e0 e0
    have hcs : (Path.refl (xs 0)).cast e0 e0 = Path.refl p₀ := by
      apply Path.ext
      funext u
      show ((Path.refl (xs 0)).cast e0 e0) u = p₀
      rw [Path.cast_coe]
      exact hxs0
    have hc2 : (Path.cast C rfl hl).cast e0 e0 = Path.cast C e0 eN := by
      apply Path.ext
      funext u
      simp only [Path.cast_coe]
    rwa [hc2, hcs] at h
  exact hpath.symm.trans h4

theorem simplyConnectedSpace_of_isOpen_cover {Z : Type*} [TopologicalSpace Z] {A B : Set Z}
    (hAo : IsOpen A) (hBo : IsOpen B) (hAB : A ∪ B = Set.univ)
    (hA : SimplyConnectedSpace ↥A) (hB : SimplyConnectedSpace ↥B)
    (hI : PathConnectedSpace ↥(A ∩ B)) : SimplyConnectedSpace Z := by
  have hAs : IsSimplyConnected A := hA
  have hBs : IsSimplyConnected B := hB
  have hAi : IsPathConnected A := IsSimplyConnected.isPathConnected hAs
  have hBi : IsPathConnected B := IsSimplyConnected.isPathConnected hBs
  have hIi : IsPathConnected (A ∩ B) := isPathConnected_iff_pathConnectedSpace.mpr hI
  have hZpc : PathConnectedSpace Z := pathConnectedSpace_of_cover hAB hAi hBi hIi.nonempty
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨hZpc, fun x γ => ?_⟩
  obtain ⟨p₀, hp₀⟩ := hIi.nonempty
  obtain ⟨ρ⟩ := hZpc.joined x p₀
  exact homotopic_refl_of_trans_conj ρ
    (loop_nullhomotopic hAo hBo hAB hAs hBs hIi p₀ hp₀ ((ρ.symm.trans γ).trans ρ))

theorem simplyConnectedSpace_of_isOpen_union {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUo : IsOpen U) (hVo : IsOpen V)
    (hU : SimplyConnectedSpace ↥U) (hV : SimplyConnectedSpace ↥V)
    (hI : PathConnectedSpace ↥(U ∩ V)) : SimplyConnectedSpace ↥(U ∪ V) := by
  refine simplyConnectedSpace_of_isOpen_cover
    (A := Subtype.val ⁻¹' U) (B := Subtype.val ⁻¹' V) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hUo.preimage continuous_subtype_val
  · exact hVo.preimage continuous_subtype_val
  · ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      rcases y.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
  · exact simplyConnectedSpace_preimage_subtype_val (s := U) (W := U ∪ V)
      (fun x hx => Or.inl hx) hU
  · exact simplyConnectedSpace_preimage_subtype_val (s := V) (W := U ∪ V)
      (fun x hx => Or.inr hx) hV
  · rw [← Set.preimage_inter]
    exact pathConnectedSpace_preimage_subtype_val (s := U ∩ V) (W := U ∪ V)
      (fun x hx => Or.inl hx.1) hI

end Work.SimplyConnected.ABS
