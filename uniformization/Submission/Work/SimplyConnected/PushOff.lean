import Mathlib
import Submission.Work.SimplyConnected.ABS.simplyConnectedSpace_of_isOpen_union
import Submission.Work.SimplyConnected.ABS.concat_conj
import Submission.Work.SimplyConnected.ABS.homotopic_cast_of_trans_const

/-!
# Pushing a loop off a simply connected piece

Let `U`, `D` be open sets covering a topological space `X`, with `U` path connected, `U ∩ D` path
connected and `D` simply connected.  If a base point `p₀` lies in `U` but not in `D`, then every
loop at `p₀` is homotopic (relative to the base point) to a loop whose image lies in `U`.

This is the surjectivity half of van Kampen for the cover `{U, D}` in the asymmetric situation
where the base point is not in `D`.  It is the "push a loop off a point" step of the surjectivity
of `π₁(X ∖ {z₀}) → π₁(X)` for a Riemann surface `X`, where `D` is a simply connected chart ball
around `z₀` and `p₀ ≠ z₀`.

The proof is the standard one and follows the file
`Submission/Work/SimplyConnected/ABS/simplyConnectedSpace_of_isOpen_union.lean` closely: subdivide
`γ` into finitely many pieces lying in `U` or in `D`; choose a point `q ∈ U ∩ D` and, for every
breakpoint, a whisker from `q`; conjugate each piece into a loop at `q`; the conjugated loops that
lie in `D` are null-homotopic; and the telescoping identity produces a loop in `U` homotopic
to `γ`.
-/

open scoped unitInterval

noncomputable section

namespace Work.SimplyConnected

/-- **Concatenation of paths lying in a set.**  If all the pieces `F k` of a concatenation have
image in `s` and the initial point of the concatenation lies in `s`, then the concatenation has
image in `s`. -/
theorem Path.concat_mem {Z : Type*} [TopologicalSpace Z] {s : Set Z} :
    ∀ (n : ℕ) (p : Fin (n + 1) → Z) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)),
      p 0 ∈ s → (∀ (k : Fin n) (u : unitInterval), F k u ∈ s) →
      ∀ u : unitInterval, Path.concat p F u ∈ s := by
  intro n
  induction n with
  | zero =>
      intro p F hp0 _ u
      rw [Path.concat_zero]
      exact hp0
  | succ n ih =>
      intro p F hp0 hF u
      rw [Path.concat_succ]
      refine ABS.Path.trans_mem _ _ ?_ ?_ u
      · exact ih (fun i => p (Fin.castSucc i)) (fun k => F (Fin.castSucc k))
          (by simpa using hp0) (fun k v => hF (Fin.castSucc k) v)
      · exact fun v => hF (Fin.last n) v

/-- **Groupoid algebra.**  If the loop `g ⬝ (C ⬝ gN⁻¹)` at `b` is homotopic to `P`, then `C` is
homotopic to `g⁻¹ ⬝ P ⬝ gN`. -/
theorem homotopic_of_trans_conj_eq {Z : Type*} [TopologicalSpace Z] {a b c : Z}
    (g : Path b a) (C : Path a c) (gN : Path b c) (P : Path b b)
    (h : Path.Homotopic (g.trans (C.trans gN.symm)) P) :
    Path.Homotopic C ((g.symm.trans P).trans gN) := by
  -- `(g⁻¹ ⬝ (g ⬝ (C ⬝ gN⁻¹))) ⬝ gN` is homotopic to `C`
  have step1 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      (g.symm.trans ((g.trans (C.trans gN.symm)).trans gN)) :=
    Path.Homotopic.trans_assoc g.symm (g.trans (C.trans gN.symm)) gN
  have step2 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      (g.symm.trans (g.trans ((C.trans gN.symm).trans gN))) :=
    step1.trans (Path.Homotopic.hcomp (Path.Homotopic.refl g.symm)
      (Path.Homotopic.trans_assoc g (C.trans gN.symm) gN))
  have step3 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      (g.symm.trans (g.trans (C.trans (gN.symm.trans gN)))) :=
    step2.trans (Path.Homotopic.hcomp (Path.Homotopic.refl g.symm)
      (Path.Homotopic.hcomp (Path.Homotopic.refl g)
        (Path.Homotopic.trans_assoc C gN.symm gN)))
  have step4 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      (g.symm.trans (g.trans (C.trans (Path.refl c)))) :=
    step3.trans (Path.Homotopic.hcomp (Path.Homotopic.refl g.symm)
      (Path.Homotopic.hcomp (Path.Homotopic.refl g)
        (Path.Homotopic.hcomp (Path.Homotopic.refl C) (Path.Homotopic.symm_trans gN))))
  have step5 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      (g.symm.trans (g.trans C)) :=
    step4.trans (Path.Homotopic.hcomp (Path.Homotopic.refl g.symm)
      (Path.Homotopic.hcomp (Path.Homotopic.refl g) (Path.Homotopic.trans_refl C)))
  have step6 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      ((g.symm.trans g).trans C) :=
    step5.trans (Path.Homotopic.trans_assoc g.symm g C).symm
  have step7 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      ((Path.refl a).trans C) :=
    step6.trans (Path.Homotopic.hcomp (Path.Homotopic.symm_trans g) (Path.Homotopic.refl C))
  have step8 : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN) C :=
    step7.trans (Path.Homotopic.refl_trans C)
  -- and replacing the inner loop by `P` changes nothing up to homotopy
  have stepP : Path.Homotopic ((g.symm.trans (g.trans (C.trans gN.symm))).trans gN)
      ((g.symm.trans P).trans gN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl g.symm) h)
      (Path.Homotopic.refl gN)
  exact step8.symm.trans stepP

/-- **A loop of `X = U ∪ D`, with `D` simply connected and off the base point, is homotopic to a
loop in `U`.** -/
theorem exists_path_homotopic_mem_of_open_cover {X : Type*} [TopologicalSpace X]
    {U D : Set X} (hUo : IsOpen U) (hDo : IsOpen D) (hcover : U ∪ D = Set.univ)
    (hU : IsPathConnected U) (hUD : IsPathConnected (U ∩ D)) (hD : IsSimplyConnected D)
    {p₀ : X} (hp₀U : p₀ ∈ U) (hp₀D : p₀ ∉ D) (γ : Path p₀ p₀) :
    ∃ γ' : Path p₀ p₀, (∀ t, γ' t ∈ U) ∧ Path.Homotopic γ γ' := by
  classical
  obtain ⟨n, t, S, hn, ht0, htn, htmono, hSAB, hSuniv, hSsub⟩ :=
    ABS.exists_partition_nat hUo hDo hcover γ
  obtain ⟨q, hqUD⟩ := hUD.nonempty
  have hqU : q ∈ U := hqUD.1
  have hqD : q ∈ D := hqUD.2
  let T : ℕ → Set X := fun k => if _ : k < n then S k else Set.univ
  have hTpiece : ∀ k, k < n → T k = U ∨ T k = D := by
    intro k hk
    dsimp only [T]
    rw [dif_pos hk]
    exact hSAB k hk
  have hTuniv : ∀ k, n ≤ k → T k = Set.univ := by
    intro k hk
    dsimp only [T]
    exact dif_neg (by omega)
  have hTmem : ∀ k, T k = U ∨ T k = D ∨ T k = Set.univ := by
    intro k
    by_cases hk : k < n
    · rcases hTpiece k hk with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by dsimp only [T]; exact dif_neg hk))
  let tF : Fin (n + 1) → ↥unitInterval := fun i => t i.val
  let xs : Fin (n + 1) → X := fun i => γ (t i.val)
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
  -- the first and last pieces lie in `U`, because `p₀ ∈ U` but `p₀ ∉ D`
  have hS0 : S 0 = U := by
    have h0 : γ (t 0) ∈ S 0 := hSsub 0 hn ⟨le_rfl, htmono (Nat.le_succ 0)⟩
    rw [ht0, γ.source] at h0
    rcases hSAB 0 hn with h | h
    · exact h
    · exact absurd (h ▸ h0) hp₀D
  have hSlast : S (n - 1) = U := by
    have h1 : γ (t n) ∈ S (n - 1) := by
      refine hSsub (n - 1) (by omega) ?_
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact ⟨htmono (by omega), le_rfl⟩
    rw [htn, γ.target] at h1
    rcases hSAB (n - 1) (by omega) with h | h
    · exact h
    · exact absurd (h ▸ h1) hp₀D
  have hT0 : T 0 = U := by
    dsimp only [T]
    rw [dif_pos hn, hS0]
  have hTlast : T (n - 1) = U := by
    dsimp only [T]
    rw [dif_pos (by omega : n - 1 < n), hSlast]
  -- path connectivity of the intersections `T (i-1) ∩ T i`
  have hDpc : IsPathConnected D := hD.isPathConnected
  have hMpc : ∀ i : Fin (n + 1), IsPathConnected (T (i.val - 1) ∩ T i.val) := by
    intro i
    exact ABS.isPathConnected_inter_of (hTpiece (i.val - 1) (by omega)) (hTmem i.val)
      hU hDpc hUD
  have hqT : ∀ k : ℕ, q ∈ T k := by
    intro k
    rcases hTmem k with h | h | h
    · rw [h]; exact hqU
    · rw [h]; exact hqD
    · rw [h]; exact Set.mem_univ _
  -- whiskers from `q` to every breakpoint
  have hgs_exists : ∀ i : Fin (n + 1),
      ∃ g : Path q (xs i), ∀ u, g u ∈ T (i.val - 1) ∩ T i.val :=
    fun i => (hMpc i).joinedIn q ⟨hqT _, hqT _⟩ (xs i) ⟨hxsTim1 i, hxsT i⟩
  let gs : (i : Fin (n + 1)) → Path q (xs i) := fun i => Classical.choose (hgs_exists i)
  have hgs_mem : ∀ (i : Fin (n + 1)) (u : ↥unitInterval),
      gs i u ∈ T (i.val - 1) ∩ T i.val := fun i => Classical.choose_spec (hgs_exists i)
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
  let r : (k : Fin n) → Path q q :=
    fun k => (gs k.castSucc).trans ((cs k).trans (gs k.succ).symm)
  have hr_mem : ∀ (k : Fin n) (u : ↥unitInterval), r k u ∈ S k.val := by
    intro k u
    dsimp only [r]
    exact ABS.Path.trans_mem (gs k.castSucc) ((cs k).trans (gs k.succ).symm)
      (fun v => hM1 k _ (hgs_mem (k.castSucc) v))
      (ABS.Path.trans_mem (cs k) (gs k.succ).symm (fun v => hcs_mem k v)
        (ABS.Path.symm_mem (gs k.succ) (fun v => hM2 k _ (hgs_mem (k.succ) v)))) u
  -- replace the pieces lying in `D` by constant loops
  let r' : (k : Fin n) → Path q q := fun k => if S k.val = U then r k else Path.refl q
  have hr'_hom : ∀ k : Fin n, Path.Homotopic (r k) (r' k) := by
    intro k
    dsimp only [r']
    by_cases hk : S k.val = U
    · rw [if_pos hk]
    · rw [if_neg hk]
      have hDk : S k.val = D := by
        rcases hSAB k.val k.isLt with h | h
        · exact absurd h hk
        · exact h
      exact ABS.loop_homotopic_refl_of_isSimplyConnected (s := D) (hDk ▸ hD) (r k)
        (fun u => hDk ▸ hr_mem k u)
  have hr'_mem : ∀ (k : Fin n) (u : ↥unitInterval), r' k u ∈ U := by
    intro k u
    dsimp only [r']
    by_cases hk : S k.val = U
    · rw [if_pos hk]
      exact hk ▸ hr_mem k u
    · rw [if_neg hk]
      exact hqU
  have hconcat : Path.Homotopic (Path.concat (fun _ : Fin (n + 1) => q) r)
      (Path.concat (fun _ : Fin (n + 1) => q) r') :=
    Path.Homotopic.concat_hcomp (fun _ : Fin (n + 1) => q) r r' hr'_hom
  have htel := ABS.concat_conj n q xs gs cs
  have h1 : Path.Homotopic ((gs 0).trans (C.trans (gs (Fin.last n)).symm))
      (Path.concat (fun _ : Fin (n + 1) => q) r') := htel.symm.trans hconcat
  have hC : Path.Homotopic C
      (((gs 0).symm.trans (Path.concat (fun _ : Fin (n + 1) => q) r')).trans
        (gs (Fin.last n))) :=
    homotopic_of_trans_conj_eq (gs 0) C (gs (Fin.last n)) _ h1
  -- the concatenation of the pieces is homotopic to `γ`
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
  have hgs0_mem : ∀ v : ↥unitInterval, gs 0 v ∈ U := by
    intro v
    have h := (hgs_mem 0 v).1
    simp only [Fin.val_zero, Nat.zero_sub] at h
    rwa [hT0] at h
  have hgsn_mem : ∀ v : ↥unitInterval, gs (Fin.last n) v ∈ U := by
    intro v
    have h := (hgs_mem (Fin.last n) v).1
    rw [Fin.val_last] at h
    rwa [hTlast] at h
  have hP_mem : ∀ v : ↥unitInterval, Path.concat (fun _ : Fin (n + 1) => q) r' v ∈ U :=
    Path.concat_mem _ _ _ hqU hr'_mem
  refine ⟨Path.cast (((gs 0).symm.trans (Path.concat (fun _ : Fin (n + 1) => q) r')).trans
    (gs (Fin.last n))) e0 eN, ?_, ?_⟩
  · intro u
    rw [Path.cast_coe]
    exact ABS.Path.trans_mem _ _
      (ABS.Path.trans_mem (gs 0).symm _ (ABS.Path.symm_mem (gs 0) hgs0_mem) hP_mem)
      hgsn_mem u
  · exact hpath.symm.trans (Path.Homotopic.pathCast hC e0 eN)

end Work.SimplyConnected
