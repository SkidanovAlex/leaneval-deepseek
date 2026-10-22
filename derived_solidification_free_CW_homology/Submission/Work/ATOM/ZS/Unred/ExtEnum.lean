import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.ZS.Data
import Submission.Work.ATOM.ZS.Topo.Maps

/-!
# The extended enumeration and functions for the *unreduced* null sequence on `ℤ[S]`

For the unreduced null-sequence data on `ℤ[S]` one needs an enumeration of `D = ⋃ₙ Aₙ` that
contains the base point `s₀` (`Work.ATOM.aEx` below is `s₀, a 0, a 1, …`), because `ψ` is defined
by looking up the index of `e_k x` and `e_0 x` can be `s₀`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint

noncomputable section

namespace Work.ATOM

variable (S : LightProfinite.{0}) [Infinite S]

/-! ## Elementary level facts -/

/-- The sets `A n` are monotone. -/
lemma A_mono_le {m n : ℕ} (h : m ≤ n) : A S m ⊆ A S n := by
  induction n, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih => exact ih.trans ((levelData S).A_mono k)

/-- `y ∈ B k` for `y` of finite level iff the level of `y` is `k`. -/
lemma mem_B_iff_lv {y : ↥S} (hy : y ∈ levelSet S) (k : ℕ) :
    y ∈ B S k ↔ (levelData S).lv y = k := by
  have hmem : y ∈ A S ((levelData S).lv y) := (levelData S).lv_mem y hy
  by_cases hk : k = 0
  · subst hk
    rw [B, if_pos rfl]
    exact ⟨fun h => le_antisymm (levelData_lv_le (S := S) h) (Nat.zero_le _),
      fun h => h ▸ hmem⟩
  · rw [B, if_neg hk]
    constructor
    · rintro ⟨h1, h2⟩
      refine le_antisymm (levelData_lv_le (S := S) h1) ?_
      by_contra hlt
      exact h2 (A_mono_le S (by omega : (levelData S).lv y ≤ k - 1) hmem)
    · intro h
      exact ⟨h ▸ hmem, fun hcon => absurd (levelData_lv_le (S := S) hcon) (by omega)⟩

lemma B_subset_levelSet (k : ℕ) : B S k ⊆ levelSet S := by
  intro y hy
  by_cases hk : k = 0
  · subst hk
    rw [B, if_pos rfl] at hy
    exact Set.mem_iUnion.mpr ⟨0, hy⟩
  · rw [B, if_neg hk] at hy
    exact Set.mem_iUnion.mpr ⟨k, hy.1⟩

/-! ## The extended enumeration -/

/-- The enumeration of `D = ⋃ₙ Aₙ` starting with the base point: `aEx 0 = s₀` and
`aEx (j+1) = a j`. -/
def aEx (j : ℕ) : ↥S := if j = 0 then (levelData S).s₀ else (levelData S).a (j - 1)

@[simp] lemma aEx_zero : aEx S 0 = (levelData S).s₀ := by simp [aEx]

@[simp] lemma aEx_succ (j : ℕ) : aEx S (j + 1) = (levelData S).a j := by simp [aEx]

/-- The level of the `j`-th point of the extended enumeration. -/
def lvEx (j : ℕ) : ℕ := (levelData S).lv (aEx S j)

lemma lvEx_zero : lvEx S 0 = 0 := by
  have hmem : aEx S 0 ∈ A S 0 := by rw [aEx_zero]; exact (levelData S).mem_A0
  by_contra h
  have hlt : 0 < lvEx S 0 := Nat.pos_of_ne_zero h
  exact (levelData S).lv_min (aEx S 0) (Set.mem_iUnion.mpr ⟨0, hmem⟩) 0 hlt hmem

@[simp] lemma lvEx_succ (j : ℕ) : lvEx S (j + 1) = lvl S j := rfl

lemma aEx_injective : Function.Injective (aEx S) := by
  intro i j hij
  match i, j with
  | 0, 0 => rfl
  | 0, k + 1 =>
    exfalso
    have h : (levelData S).s₀ = (levelData S).a k := by simpa using hij
    exact levelData_a_ne (S := S) k h.symm
  | k + 1, 0 =>
    exfalso
    have h : (levelData S).a k = (levelData S).s₀ := by simpa using hij
    exact levelData_a_ne (S := S) k h
  | k + 1, l + 1 =>
    have h : (levelData S).a k = (levelData S).a l := by simpa using hij
    rw [levelData_a_inj (S := S) h]

lemma aEx_mem (j : ℕ) : aEx S j ∈ levelSet S := by
  match j with
  | 0 => rw [aEx_zero]; exact Set.mem_iUnion.mpr ⟨0, (levelData S).mem_A0⟩
  | k + 1 => rw [aEx_succ]; exact levelData_a_mem (S := S) k

lemma aEx_range : Set.range (aEx S) = levelSet S := by
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    exact aEx_mem S j
  · intro hy
    rcases (levelData_mem_levelSet_iff (S := S) y).mp hy with ⟨j, rfl⟩ | rfl
    · exact ⟨j + 1, by rw [aEx_succ]⟩
    · exact ⟨0, aEx_zero S⟩

lemma lvEx_mem (j : ℕ) : aEx S j ∈ A S (lvEx S j) :=
  (levelData S).lv_mem (aEx S j) (aEx_mem S j)

lemma lvEx_min (j : ℕ) {m : ℕ} (hm : m < lvEx S j) : aEx S j ∉ A S m :=
  (levelData S).lv_min (aEx S j) (aEx_mem S j) m hm

lemma e_lvEx (j : ℕ) : e S (lvEx S j) (aEx S j) = aEx S j :=
  (levelData S).e_fix_A _ _ (lvEx_mem S j)

/-- The `j`-th point of the extended enumeration lies in exactly the `B k` with `k = lvEx j`. -/
lemma aEx_mem_B_iff (j k : ℕ) : aEx S j ∈ B S k ↔ lvEx S j = k :=
  mem_B_iff_lv S (aEx_mem S j) k

/-! ## The extended `ψ` -/

/-- The index of `y` in the extended enumeration (used for `y ∈ levelSet S`). -/
def idxEx (y : ↥S) : ℕ := by
  classical
  exact if y = (levelData S).s₀ then 0 else (levelData S).idx y + 1

@[simp] lemma idxEx_s₀ : idxEx S (levelData S).s₀ = 0 := by
  rw [idxEx]
  exact if_pos rfl

@[simp] lemma idxEx_a (j : ℕ) : idxEx S ((levelData S).a j) = j + 1 := by
  rw [idxEx, if_neg (levelData_a_ne (S := S) j), (levelData S).idx_a]

@[simp] lemma idxEx_aEx (j : ℕ) : idxEx S (aEx S j) = j := by
  match j with
  | 0 => exact idxEx_s₀ S
  | k + 1 => exact idxEx_a S k

lemma aEx_idxEx {y : ↥S} (hy : y ∈ levelSet S) : aEx S (idxEx S y) = y := by
  by_cases h : y = (levelData S).s₀
  · rw [h, idxEx_s₀, aEx_zero]
  · have hy' : y ∈ levelSet' S := by
      simp only [levelSet', Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hy, h⟩
    rw [idxEx, if_neg h, aEx_succ, levelData_a_idx (S := S) y hy']

/-- The function `ψ̃ : (ℕ∪{∞}) × S → ℕ∪{∞}`, the extended version of `ψ`: the index of `e_k x` in
the extended enumeration when `e_k x ∈ B_k`, and `∞` otherwise. -/
def psiExFun (p : ↥(NS S)) : ℕ∪{∞} := by
  classical
  exact p.1.elim ∞ (fun k => if e S k p.2 ∈ B S k then (idxEx S (e S k p.2) : ℕ∪{∞}) else ∞)

@[simp] lemma mkNS_fst (k : ℕ∪{∞}) (x : ↥S) : (mkNS S k x).1 = k := rfl

@[simp] lemma mkNS_snd (k : ℕ∪{∞}) (x : ↥S) : (mkNS S k x).2 = x := rfl

@[simp] lemma psiExFun_infty (x : ↥S) : psiExFun S (mkNS S ∞ x) = ∞ := by
  rw [psiExFun]
  simp

lemma psiExFun_of (k : ℕ) {x : ↥S} (h : e S k x ∈ B S k) :
    psiExFun S (mkNS S ((k : ℕ) : ℕ∪{∞}) x) = (idxEx S (e S k x) : ℕ∪{∞}) := by
  classical
  show (if e S k x ∈ B S k then (idxEx S (e S k x) : ℕ∪{∞}) else ∞) =
    (idxEx S (e S k x) : ℕ∪{∞})
  exact if_pos h

lemma psiExFun_eq_infty (k : ℕ) {x : ↥S} (h : e S k x ∉ B S k) :
    psiExFun S (mkNS S ((k : ℕ) : ℕ∪{∞}) x) = ∞ := by
  classical
  show (if e S k x ∈ B S k then (idxEx S (e S k x) : ℕ∪{∞}) else ∞) = ∞
  exact if_neg h

/-- **The value of `ψ̃` on the cover.**  `ψ̃(k,x) = j` holds exactly for the points with
`k = lvEx j` and `e_{lvEx j} x = aEx j`. -/
lemma psiExFun_eq_some_iff_mkNS (j : ℕ) (k : ℕ) (x : ↥S) :
    psiExFun S (mkNS S ((k : ℕ) : ℕ∪{∞}) x) = ((j : ℕ) : ℕ∪{∞}) ↔
      lvEx S j = k ∧ e S k x = aEx S j := by
  constructor
  · intro h
    by_cases hc : e S k x ∈ B S k
    · rw [psiExFun_of S k hc] at h
      have hidx : idxEx S (e S k x) = j := OnePoint.coe_eq_coe.mp h
      have hy : e S k x ∈ levelSet S := B_subset_levelSet S k hc
      have hax : aEx S j = e S k x := by rw [← hidx]; exact aEx_idxEx S hy
      exact ⟨by rw [lvEx, hax, (mem_B_iff_lv S hy k).mp hc], hax.symm⟩
    · rw [psiExFun_eq_infty S k hc] at h
      exact absurd h (OnePoint.infty_ne_coe j)
  · rintro ⟨hk, hx⟩
    subst hk
    refine (psiExFun_of S (lvEx S j) ?_).trans ?_
    · rw [hx]; exact (aEx_mem_B_iff S j (lvEx S j)).mpr rfl
    · rw [hx, idxEx_aEx]

/-- The value of `ψ̃` at an arbitrary point of `(ℕ∪{∞}) × S`. -/
lemma psiExFun_eq_some_iff (j : ℕ) (p : ↥(NS S)) :
    psiExFun S p = ((j : ℕ) : ℕ∪{∞}) ↔
      p.1 = ((lvEx S j : ℕ) : ℕ∪{∞}) ∧ e S (lvEx S j) p.2 = aEx S j := by
  by_cases h1 : p.1 = ∞
  · have hp : psiExFun S p = ∞ := by rw [psiExFun, h1]; simp
    exact ⟨fun h => absurd (hp ▸ h) (OnePoint.infty_ne_coe j),
      fun h => absurd (h1 ▸ h.1) (OnePoint.infty_ne_coe (lvEx S j))⟩
  · obtain ⟨k, hk⟩ := OnePoint.ne_infty_iff_exists.mp h1
    have hpe : p = mkNS S ((k : ℕ) : ℕ∪{∞}) p.2 := Prod.ext hk.symm rfl
    rw [hpe]
    show (psiExFun S (mkNS S ((k : ℕ) : ℕ∪{∞}) p.2) = ((j : ℕ) : ℕ∪{∞})) ↔
      (((k : ℕ) : ℕ∪{∞}) = ((lvEx S j : ℕ) : ℕ∪{∞}) ∧ e S (lvEx S j) p.2 = aEx S j)
    rw [psiExFun_eq_some_iff_mkNS]
    exact ⟨fun ⟨h, hx⟩ => ⟨(congrArg (fun n : ℕ => ((n : ℕ) : ℕ∪{∞})) h).symm, h.symm ▸ hx⟩,
      fun ⟨h, hx⟩ => ⟨(OnePoint.coe_eq_coe.mp h).symm,
        (OnePoint.coe_eq_coe.mp h).symm ▸ hx⟩⟩

/-- The fibre of `ψ̃` over `j` as a set. -/
lemma psiExFun_preimage_singleton (j : ℕ) :
    psiExFun S ⁻¹' {((j : ℕ) : ℕ∪{∞})} =
      (fun p : ↥(NS S) => p.1) ⁻¹' {((lvEx S j : ℕ) : ℕ∪{∞})} ∩
        (fun p : ↥(NS S) => p.2) ⁻¹' {x : ↥S | e S (lvEx S j) x = aEx S j} := by
  ext p
  rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact psiExFun_eq_some_iff S j p

/-- The fibre of `e_m` over a point is clopen. -/
lemma isClopen_preimage_e (m : ℕ) (y : ↥S) : IsClopen {x : ↥S | e S m x = y} := by
  by_cases hy : y ∈ A S m
  · have hset : {x : ↥S | e S m x = y} = S.proj m ⁻¹' {S.proj m y} := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        have h2 := congrArg (S.proj m) h
        rwa [e_apply, sig_proj_apply] at h2
      · intro h
        have h' : e S m x = e S m y := by rw [e_apply, e_apply, h]
        rwa [(levelData S).e_fix_A m y hy] at h'
    rw [hset]
    exact (isClopen_discrete _).preimage (by fun_prop)
  · have hset : {x : ↥S | e S m x = y} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hy ⟨x, h⟩
    rw [hset]
    exact isClopen_empty

/-- Continuity of the extended `ψ`. -/
theorem psiExFun_continuous : Continuous (psiExFun S) := by
  rw [continuous_onePoint_iff_isClopen]
  intro j
  rw [psiExFun_preimage_singleton]
  exact IsClopen.inter ((isClopen_singleton_some (lvEx S j)).preimage continuous_fst)
    ((isClopen_preimage_e S (lvEx S j) (aEx S j)).preimage continuous_snd)

/-- The extended `ψ` as a morphism of light profinite sets. -/
def psiEx : NS S ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨psiExFun S, psiExFun_continuous S⟩

@[simp] lemma psiEx_apply (p : ↥(NS S)) : psiEx S p = psiExFun S p := rfl

lemma psiEx_mkNS_of (k : ℕ) {x : ↥S} (h : e S k x ∈ B S k) :
    psiEx S (mkNS S ((k : ℕ) : ℕ∪{∞}) x) = (idxEx S (e S k x) : ℕ∪{∞}) :=
  psiExFun_of S k h

/-! ## The extended `φ_P` -/

/-- The extended `φ_P : (ℕ∪{∞})² → ℕ∪{∞}`, `(k,j) ↦ j` if `k ≤ lvEx j`, else `∞`. -/
def phiPExFun (p : ↥NS2) : ℕ∪{∞} :=
  p.1.elim ∞ fun k => p.2.elim ∞ fun j => if k ≤ lvEx S j then (j : ℕ∪{∞}) else ∞

@[simp] lemma mkNS2_fst (k j : ℕ∪{∞}) : (mkNS2 k j).1 = k := rfl

@[simp] lemma mkNS2_snd (k j : ℕ∪{∞}) : (mkNS2 k j).2 = j := rfl

@[simp] lemma phiPExFun_infty_left (q : ↥(ℕ∪{∞})) : phiPExFun S (mkNS2 ∞ q) = ∞ := by
  show (∞ : ℕ∪{∞}) = ∞
  rfl

@[simp] lemma phiPExFun_some_infty (k : ℕ) :
    phiPExFun S (mkNS2 ((k : ℕ) : ℕ∪{∞}) ∞) = ∞ := by
  show (∞ : ℕ∪{∞}) = ∞
  rfl

lemma phiPExFun_infty_right (q : ↥(ℕ∪{∞})) : phiPExFun S (mkNS2 q ∞) = ∞ := by
  rcases q with _ | k
  · exact phiPExFun_infty_left S _
  · exact phiPExFun_some_infty S k

lemma phiPExFun_some_some (k j : ℕ) :
    phiPExFun S (mkNS2 ((k : ℕ) : ℕ∪{∞}) ((j : ℕ) : ℕ∪{∞})) =
      (if k ≤ lvEx S j then ((j : ℕ) : ℕ∪{∞}) else ∞) := by
  classical
  show (if k ≤ lvEx S j then ((j : ℕ) : ℕ∪{∞}) else ∞) =
    (if k ≤ lvEx S j then ((j : ℕ) : ℕ∪{∞}) else ∞)
  rfl

lemma phiPExFun_some_some_of_le {k j : ℕ} (h : k ≤ lvEx S j) :
    phiPExFun S (mkNS2 ((k : ℕ) : ℕ∪{∞}) ((j : ℕ) : ℕ∪{∞})) = ((j : ℕ) : ℕ∪{∞}) := by
  rw [phiPExFun_some_some, if_pos h]

lemma phiPExFun_some_some_of_lt {k j : ℕ} (h : lvEx S j < k) :
    phiPExFun S (mkNS2 ((k : ℕ) : ℕ∪{∞}) ((j : ℕ) : ℕ∪{∞})) = ∞ := by
  rw [phiPExFun_some_some, if_neg (by omega)]

/-- The fibre of the extended `φ_P` over a finite index. -/
lemma phiPExFun_eq_some_iff (j : ℕ) (p : ↥NS2) :
    phiPExFun S p = ((j : ℕ) : ℕ∪{∞}) ↔
      ∃ k : ℕ, k ≤ lvEx S j ∧ p = mkNS2 ((k : ℕ) : ℕ∪{∞}) ((j : ℕ) : ℕ∪{∞}) := by
  have key : ∀ k m : ℕ, phiPExFun S (mkNS2 ((k : ℕ) : ℕ∪{∞}) ((m : ℕ) : ℕ∪{∞})) =
      ((j : ℕ) : ℕ∪{∞}) ↔ ∃ k' : ℕ, k' ≤ lvEx S j ∧
        mkNS2 ((k : ℕ) : ℕ∪{∞}) ((m : ℕ) : ℕ∪{∞}) =
          mkNS2 ((k' : ℕ) : ℕ∪{∞}) ((j : ℕ) : ℕ∪{∞}) := by
    intro k m
    rw [phiPExFun_some_some]
    by_cases h : k ≤ lvEx S m
    · rw [if_pos h]
      constructor
      · intro hj
        exact ⟨k, OnePoint.coe_eq_coe.mp hj ▸ h, Prod.ext rfl hj⟩
      · rintro ⟨k', -, hk'⟩
        have h2'' := congrArg (fun q : ↥NS2 => q.2) hk'
        rw [mkNS2_snd, mkNS2_snd] at h2''
        exact h2''
    · rw [if_neg h]
      constructor
      · intro hc
        exact absurd hc (OnePoint.infty_ne_coe j)
      · rintro ⟨k', hk', hk''⟩
        have h1'' := congrArg (fun q : ↥NS2 => q.1) hk''
        rw [mkNS2_fst, mkNS2_fst] at h1''
        have h2'' := congrArg (fun q : ↥NS2 => q.2) hk''
        rw [mkNS2_snd, mkNS2_snd] at h2''
        have hkk : k = k' := by simpa only [OnePoint.coe_eq_coe] using h1''
        have hmj : m = j := by simpa only [OnePoint.coe_eq_coe] using h2''
        have hkj : ¬ (k' ≤ lvEx S j) := by
          intro hle
          rw [← hkk, ← hmj] at hle
          exact h hle
        exact absurd hk' hkj
  by_cases h1 : p.1 = ∞
  · have hp : phiPExFun S p = ∞ := by rw [phiPExFun, h1]; simp
    refine ⟨fun h => absurd (hp ▸ h) (OnePoint.infty_ne_coe j), fun h => ?_⟩
    obtain ⟨k, -, hk⟩ := h
    have h1' := h1
    rw [hk] at h1'
    exact absurd h1' (OnePoint.coe_ne_infty k)
  · obtain ⟨k, hk⟩ := OnePoint.ne_infty_iff_exists.mp h1
    by_cases h2 : p.2 = ∞
    · have hp : phiPExFun S p = ∞ := by rw [phiPExFun, ← hk, h2]; simp
      refine ⟨fun h => absurd (hp ▸ h) (OnePoint.infty_ne_coe j), fun h => ?_⟩
      obtain ⟨k', -, hk'⟩ := h
      have h2' : p.2 = ((j : ℕ) : ℕ∪{∞}) := by rw [hk', mkNS2_snd]
      exact absurd (h2.symm.trans h2') (OnePoint.infty_ne_coe j)
    · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp h2
      have hpm : p = mkNS2 ((k : ℕ) : ℕ∪{∞}) ((m : ℕ) : ℕ∪{∞}) := Prod.ext hk.symm hm.symm
      constructor
      · intro h
        obtain ⟨k', hk', hk''⟩ := (key k m).mp (by rw [← hpm]; exact h)
        exact ⟨k', hk', hpm.trans hk''⟩
      · rintro ⟨k', hk', hk''⟩
        rw [hpm]
        exact (key k m).mpr ⟨k', hk', hpm.symm.trans hk''⟩

/-- Continuity of the extended `φ_P`. -/
theorem phiPExFun_continuous : Continuous (phiPExFun S) := by
  rw [continuous_onePoint_iff_isClopen]
  intro j
  have hset : phiPExFun S ⁻¹' {((j : ℕ) : ℕ∪{∞})} =
      ⋃ k ∈ Set.Iic (lvEx S j), ((fun p : ↥NS2 => p.1) ⁻¹' {((k : ℕ) : ℕ∪{∞})} ∩
        (fun p : ↥NS2 => p.2) ⁻¹' {((j : ℕ) : ℕ∪{∞})}) := by
    ext p
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion₂, phiPExFun_eq_some_iff]
    constructor
    · rintro ⟨k, hk, hp⟩
      refine ⟨k, hk, ?_, ?_⟩
      · rw [Set.mem_preimage, Set.mem_singleton_iff, hp]
      · rw [Set.mem_preimage, Set.mem_singleton_iff, hp]
    · rintro ⟨k, hk, h1, h2⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
      exact ⟨k, hk, Prod.ext h1 h2⟩
  rw [hset]
  refine Set.Finite.isClopen_biUnion (Set.finite_Iic _) fun k _ => IsClopen.inter ?_ ?_
  · exact (isClopen_singleton_some k).preimage continuous_fst
  · exact (isClopen_singleton_some j).preimage continuous_snd

/-- The extended `φ_P` as a morphism of light profinite sets. -/
def phiPEx : NS2 ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨phiPExFun S, phiPExFun_continuous S⟩

@[simp] lemma phiPEx_apply (p : ↥NS2) : phiPEx S p = phiPExFun S p := rfl


/-! ## The extended cover `T̃' = {(j, aEx j)} ∪ {∞} × S` -/

/-- The cover of `(ℕ∪{∞}) × S` given by the graph of the extended enumeration and the fibre at
`∞`. -/
def tSetEx : Set ↥(NS S) :=
  {p | p.1 = ∞ ∨ ∃ j : ℕ, p.1 = ((j : ℕ) : ℕ∪{∞}) ∧ p.2 = aEx S j}

lemma mem_tSetEx_infty (x : ↥S) : mkNS S ∞ x ∈ tSetEx S := Or.inl rfl

lemma mem_tSetEx_graph (j : ℕ) :
    mkNS S ((j : ℕ) : ℕ∪{∞}) (aEx S j) ∈ tSetEx S := Or.inr ⟨j, rfl, rfl⟩

lemma tSetEx_second_eq {p : ↥(NS S)} (hp : p ∈ tSetEx S) {j : ℕ}
    (hj : p.1 = ((j : ℕ) : ℕ∪{∞})) : p.2 = aEx S j := by
  rcases hp with h | ⟨j', hj', h2⟩
  · exact absurd (hj ▸ h) (by simp)
  · rw [hj] at hj'
    rw [OnePoint.coe_eq_coe] at hj'
    rw [hj', h2]

/-- `T̃'` is closed. -/
theorem tSetEx_isClosed : IsClosed (tSetEx S) := by
  rw [← isOpen_compl_iff]
  have hcompl : (tSetEx S)ᶜ = ⋃ j : ℕ, {p : ↥(NS S) | p.1 = ((j : ℕ) : ℕ∪{∞})} ∩
      {p : ↥(NS S) | p.2 ≠ aEx S j} := by
    ext p
    constructor
    · intro hp
      rw [Set.mem_compl_iff] at hp
      have h1 : p.1 ≠ ∞ := fun hcon => hp (by rw [tSetEx]; exact Or.inl hcon)
      have h2 : ∀ j : ℕ, p.1 = ((j : ℕ) : ℕ∪{∞}) → p.2 ≠ aEx S j :=
        fun j hj hcon => hp (by rw [tSetEx]; exact Or.inr ⟨j, hj, hcon⟩)
      obtain ⟨j, hj⟩ := OnePoint.ne_infty_iff_exists.mp h1
      rw [Set.mem_iUnion]
      exact ⟨j, hj.symm, h2 j hj.symm⟩
    · intro hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨j, hj, h2⟩ := hp
      rw [Set.mem_ofPred_eq] at hj h2
      rw [Set.mem_compl_iff]
      intro hcon
      rw [tSetEx] at hcon
      rcases hcon with h | ⟨i, hi, hcon'⟩
      · exact OnePoint.coe_ne_infty j (hj.symm.trans h)
      · exact h2 (by rw [OnePoint.coe_eq_coe.mp (hj.symm.trans hi)]; exact hcon')
  rw [hcompl]
  refine isOpen_iUnion fun j => IsOpen.inter ?_ ?_
  · exact (isClopen_singleton_some j).2.preimage continuous_fst
  · exact isOpen_compl_singleton.preimage continuous_snd

instance instCompactSpaceTSetEx : CompactSpace ↥(tSetEx S) :=
  isCompact_iff_compactSpace.mp (tSetEx_isClosed S).isCompact

/-- The light profinite set `T̃'`. -/
def T'Ex : LightProfinite.{0} := LightProfinite.of ↥(tSetEx S)

/-- A point of `T̃'` is a pair. -/
def mkT (j : ℕ) : ↥(T'Ex S) := ⟨mkNS S ((j : ℕ) : ℕ∪{∞}) (aEx S j), mem_tSetEx_graph S j⟩

/-- The first projection `T̃' ⟶ ℕ∪{∞}`. -/
def tProjEx : T'Ex S ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The second projection `T̃' ⟶ S`. -/
def pr₂TEx : T'Ex S ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => p.1.2, continuous_snd.comp continuous_subtype_val⟩

/-- The "shift down" map `k ↦ k - 1` on `ℕ∪{∞}`, with `0 ↦ 0` and `∞ ↦ ∞`. -/
def predShiftFun : ℕ∪{∞} → ℕ∪{∞} :=
  fun k => k.elim ∞ (fun n => if n = 0 then ((0 : ℕ) : ℕ∪{∞}) else ((n - 1 : ℕ) : ℕ∪{∞}))

@[simp] lemma predShiftFun_infty : predShiftFun ∞ = ∞ := rfl

@[simp] lemma predShiftFun_zero :
    predShiftFun ((0 : ℕ) : ℕ∪{∞}) = ((0 : ℕ) : ℕ∪{∞}) := by
  rw [predShiftFun]
  simp

@[simp] lemma predShiftFun_succ (n : ℕ) :
    predShiftFun ((n + 1 : ℕ) : ℕ∪{∞}) = ((n : ℕ) : ℕ∪{∞}) := by
  rw [predShiftFun]
  simp [Nat.succ_ne_zero]

lemma predShiftFun_preimage_zero :
    predShiftFun ⁻¹' {((0 : ℕ) : ℕ∪{∞})} =
      ({((0 : ℕ) : ℕ∪{∞}), ((1 : ℕ) : ℕ∪{∞})} : Set (ℕ∪{∞})) := by
  ext k
  by_cases hk : k = ∞
  · rw [Set.mem_preimage, Set.mem_singleton_iff, hk, predShiftFun_infty]
    simp
  · obtain ⟨n, hn⟩ := OnePoint.ne_infty_iff_exists.mp hk
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← hn]
    rcases n with _ | m
    · rw [predShiftFun_zero]
      simp
    · rw [predShiftFun_succ]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, OnePoint.coe_eq_coe]
      omega

lemma predShiftFun_preimage_succ (j : ℕ) :
    predShiftFun ⁻¹' {((j + 1 : ℕ) : ℕ∪{∞})} = {((j + 2 : ℕ) : ℕ∪{∞})} := by
  ext k
  by_cases hk : k = ∞
  · rw [Set.mem_preimage, Set.mem_singleton_iff, hk, predShiftFun_infty]
    simp
  · obtain ⟨n, hn⟩ := OnePoint.ne_infty_iff_exists.mp hk
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← hn]
    rcases n with _ | m
    · rw [predShiftFun_zero]
      simp only [Set.mem_singleton_iff, OnePoint.coe_eq_coe]
      omega
    · rw [predShiftFun_succ]
      simp only [Set.mem_singleton_iff, OnePoint.coe_eq_coe]
      omega

lemma predShiftFun_continuous : Continuous predShiftFun := by
  rw [continuous_onePoint_iff_isClopen]
  intro j
  rcases j with _ | j
  · rw [predShiftFun_preimage_zero]
    exact (isClopen_singleton_some 0).union (isClopen_singleton_some 1)
  · rw [predShiftFun_preimage_succ j]
    exact isClopen_singleton_some (j + 2)

/-- The shift-down morphism `ℕ∪{∞} ⟶ ℕ∪{∞}`. -/
def predShift : ℕ∪{∞} ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨predShiftFun, predShiftFun_continuous⟩

/-- The map `T̃' ⟶ (ℕ∪{∞}) × S` which shifts the first coordinate down. -/
def shiftT : T'Ex S ⟶ NS S :=
  ConcreteCategory.ofHom
    ⟨fun p => mkNS S (predShiftFun p.1.1) p.1.2,
      Continuous.prodMk
        (predShiftFun_continuous.comp (continuous_fst.comp continuous_subtype_val))
        (continuous_snd.comp continuous_subtype_val)⟩

/-- `β̃ = β ∘ (shift)`: the restriction of `β` to the extended cover. -/
def betaTEx : T'Ex S ⟶ S := shiftT S ≫ betaN S

@[simp] lemma tProjEx_apply (p : ↥(T'Ex S)) : tProjEx S p = p.1.1 := rfl

@[simp] lemma pr₂TEx_apply (p : ↥(T'Ex S)) : pr₂TEx S p = p.1.2 := rfl

@[simp] lemma mkT_apply (j : ℕ) : (mkT S j : ↥(T'Ex S)).1 = mkNS S ((j : ℕ) : ℕ∪{∞}) (aEx S j) := rfl

@[simp] lemma tProjEx_mkT (j : ℕ) : tProjEx S (mkT S j) = ((j : ℕ) : ℕ∪{∞}) := rfl

@[simp] lemma pr₂TEx_mkT (j : ℕ) : pr₂TEx S (mkT S j) = aEx S j := rfl

@[simp] lemma betaTEx_mkT (j : ℕ) :
    betaTEx S (mkT S j) = betaFun S (mkNS S (predShiftFun ((j : ℕ) : ℕ∪{∞})) (aEx S j)) := rfl

/-- The first projection of the extended cover is surjective. -/
lemma tProjEx_surjective : Function.Surjective (tProjEx S) := by
  intro q
  rcases q with _ | j
  · exact ⟨⟨mkNS S ∞ (levelData S).s₀, mem_tSetEx_infty S _⟩, rfl⟩
  · exact ⟨mkT S j, rfl⟩

/-- The fibre of `tProjEx` over a finite index is a single point. -/
lemma tProjEx_eq_mkT {p : ↥(T'Ex S)} {j : ℕ} (h : tProjEx S p = ((j : ℕ) : ℕ∪{∞})) :
    p = mkT S j := by
  refine Subtype.ext ?_
  have h1 : p.1.1 = ((j : ℕ) : ℕ∪{∞}) := h
  have h2 : p.1.2 = aEx S j := tSetEx_second_eq S p.2 h1
  exact Prod.ext h1 h2

/-- The value of `β̃` at the `j`-th point of the cover. -/
lemma betaTEx_mkT_val (j : ℕ) :
    betaTEx S (mkT S j) = betaFun S (mkNS S (predShiftFun ((j : ℕ) : ℕ∪{∞})) (aEx S j)) := rfl

lemma betaTEx_mkT_zero :
    betaTEx S (mkT S 0) = (levelData S).s₀ := by
  rw [betaTEx_mkT, predShiftFun_zero, aEx_zero]
  rcases Nat.eq_zero_or_pos (lvl S 0) with h | h
  · rw [betaFun, OnePoint.elim_some, if_pos h]
  · rw [betaFun, OnePoint.elim_some, if_neg (by omega)]
    exact (levelData S).e_fix _

lemma betaTEx_mkT_succ (j : ℕ) :
    betaTEx S (mkT S (j + 1)) = betaFun S (mkNS S ((j : ℕ) : ℕ∪{∞}) ((levelData S).a j)) := by
  rw [betaTEx_mkT, predShiftFun_succ, aEx_succ]

end Work.ATOM
