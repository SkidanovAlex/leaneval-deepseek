/-
Third auxiliary module for `Work.SGsep.pair_separates`: the combinatorial facts about
`Data.pairKeys` (membership, no duplicates), the bridge `Data.pairCount = PInv`, and the
invariance of `PInv` under conjugation by a unimodular matrix.
-/
import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.PairAux
import Submission.Work.SGsep.PairAux2

namespace Work.SGsep
open Work.SG
open Work.SGsep.PSep
open Classical

namespace PSep

/-! ## 1. `Data.pairKeys` as the filtered product list -/

theorem map_pair_filterMap (l : List ℕ) (i : ℕ) (c : ℕ → ℕ → Bool) :
    (l.map (fun j => (i, j))).filter (fun ij => c ij.1 ij.2)
      = l.filterMap (fun j => if c i j then some (i, j) else none) := by
  induction l with
  | nil => simp
  | cons j t ih =>
    rw [List.map_cons, List.filter_cons]
    by_cases hc : c i j = true
    · rw [if_pos hc, List.filterMap_cons_some (h := by rw [if_pos hc]), ih]
    · rw [if_neg hc, List.filterMap_cons_none (h := by rw [if_neg hc]), ih]

theorem flatMap_filterMap_ite (l₁ l₂ : List ℕ) (c : ℕ → ℕ → Bool) :
    l₁.flatMap (fun i => l₂.filterMap (fun j => if c i j then some (i, j) else none))
      = (l₁.flatMap (fun i => l₂.map (fun j => (i, j)))).filter (fun ij => c ij.1 ij.2) := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.filter_append, ih]
    congr 1
    exact (map_pair_filterMap l₂ a c).symm

/-- `Data.pairKeys k kA kB` is the row-major product list filtered by the key conditions. -/
theorem pairKeys_eq_prod (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) :
    Data.pairKeys k kA kB
      = (((List.range (pn k)).flatMap (fun i => (List.range (pn k)).map (fun j => (i, j)))).filter
          (fun ij => (ekeyK k ij.1 == kA) && (ekeyK k ij.2 == kB))) := by
  rw [Data.pairKeys]
  exact flatMap_filterMap_ite (List.range (Data.repArith k.val).n)
    (List.range (Data.repArith k.val).n)
    (fun i j => (Data.ekey k.val i == kA) && (Data.ekey k.val j == kB))

theorem mem_pairKeys {k : Fin 230} {kA kB : ℤ × ℤ × ℕ} {a b : ℕ} :
    (a, b) ∈ Data.pairKeys k kA kB ↔
      a < pn k ∧ b < pn k ∧ ekeyK k a = kA ∧ ekeyK k b = kB := by
  rw [pairKeys_eq_prod, List.mem_filter, List.mem_flatMap]
  constructor
  · rintro ⟨⟨i, hi, hmem⟩, hcond⟩
    obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hjeq
    obtain ⟨rfl, rfl⟩ := hjeq
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hcond
    exact ⟨List.mem_range.mp hi, List.mem_range.mp hj, beq_iff_eq.mp h1, beq_iff_eq.mp h2⟩
  · rintro ⟨ha, hb, hka, hkb⟩
    refine ⟨⟨a, List.mem_range.mpr ha, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩⟩, ?_⟩
    rw [Bool.and_eq_true_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨hka, hkb⟩

theorem mem_pairKeys_iff {k : Fin 230} {kA kB : ℤ × ℤ × ℕ} {ij : ℕ × ℕ} :
    ij ∈ Data.pairKeys k kA kB ↔
      ij.1 < pn k ∧ ij.2 < pn k ∧ ekeyK k ij.1 = kA ∧ ekeyK k ij.2 = kB := by
  exact mem_pairKeys (k := k) (kA := kA) (kB := kB) (a := ij.1) (b := ij.2)

theorem pairKeys_nodup (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) :
    (Data.pairKeys k kA kB).Nodup := by
  rw [pairKeys_eq_prod]
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    exact List.Nodup.map (fun a b h => (Prod.mk.injEq _ _ _ _).mp h |>.2) List.nodup_range
  · refine List.Pairwise.imp ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
    intro i j hij
    show List.Disjoint (List.map (fun t => (i, t)) (List.range (pn k)))
      (List.map (fun t => (j, t)) (List.range (pn k)))
    rw [List.disjoint_left]
    intro x hx1 hx2
    obtain ⟨j₁, _, hj₁⟩ := List.mem_map.mp hx1
    obtain ⟨j₂, _, hj₂⟩ := List.mem_map.mp hx2
    have h1 : x.1 = i := by rw [← hj₁]
    have h2 : x.1 = j := by rw [← hj₂]
    exact hij (h1.symm.trans h2)

theorem pairKeys_toFinset (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) :
    (Data.pairKeys k kA kB).toFinset
      = (((Finset.range (pn k)) ×ˢ (Finset.range (pn k))).filter
          (fun ij => ekeyK k ij.1 = kA ∧ ekeyK k ij.2 = kB)) := by
  ext ij
  rw [List.mem_toFinset, mem_pairKeys_iff, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Finset.mem_range]
  tauto

/-! ## 2. `Data.pairCount` computes `PInv` -/

/-- The index-level count: key-matching index pairs whose bit pattern is `bits`. -/
noncomputable def PairCnt (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) (bits : List Bool) : ℕ :=
  (Data.pairKeys k kA kB).countP (fun ij => (pairBits k (elI k ij.1) (elI k ij.2) == bits))

theorem pairCount_eq_PairCnt (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) (bits : List Bool)
    (la : List Data.PairCert) (ca : ℕ)
    (hkey : ∀ i, i < pn k → ekeyK k i = keyE k (elI k i))
    (hbit : ∀ p : Data.PairCert, p.i < pn k → p.j < pn k → Data.PairCert.chk k p = true →
      p.bits = pairBits k (elI k p.i) (elI k p.j))
    (ha : Data.pairCount k kA kB bits la = some ca) :
    ca = PairCnt k kA kB bits := by
  have hcond : (la.map (fun p => (p.i, p.j)) == Data.pairKeys k kA kB &&
      la.all (Data.PairCert.chk k)) = true := by
    by_contra hc
    rw [Data.pairCount, if_neg hc] at ha
    exact absurd ha (by simp)
  obtain ⟨hmapb, hallb⟩ := Bool.and_eq_true_iff.mp hcond
  have hmap : la.map (fun p => (p.i, p.j)) = Data.pairKeys k kA kB := beq_iff_eq.mp hmapb
  have hall : la.all (Data.PairCert.chk k) = true := hallb
  rw [Data.pairCount, if_pos hcond] at ha
  have hca : ca = la.countP (fun p => p.bits == bits) := Option.some.injEq .. |>.mp ha.symm
  rw [hca]
  have hbits : la.countP (fun p => p.bits == bits)
      = la.countP (fun p => (pairBits k (elI k p.i) (elI k p.j) == bits)) := by
    apply List.countP_congr
    intro p hp
    have hchk : Data.PairCert.chk k p = true := List.all_eq_true.mp hall p hp
    have hmem : (p.i, p.j) ∈ Data.pairKeys k kA kB := by
      have : (p.i, p.j) ∈ la.map (fun p => (p.i, p.j)) := List.mem_map.mpr ⟨p, hp, rfl⟩
      rwa [hmap] at this
    obtain ⟨hi, hj, _, _⟩ := mem_pairKeys.mp hmem
    rw [hbit p hi hj hchk]
  rw [hbits]
  have hfun : (fun p : Data.PairCert => (pairBits k (elI k p.i) (elI k p.j) == bits))
      = (fun ij : ℕ × ℕ => (pairBits k (elI k ij.1) (elI k ij.2) == bits))
        ∘ (fun p : Data.PairCert => (p.i, p.j)) := rfl
  rw [hfun, ← List.countP_map, hmap]
  rfl

theorem PairCnt_eq_PInv (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) (bits : List Bool)
    (hkey : ∀ i, i < pn k → ekeyK k i = keyE k (elI k i))
    (hTk : Tk k = ((List.range (pn k)).map (elI k)).toFinset)
    (hinj : Set.InjOn (elI k) (Set.Iio (pn k))) :
    PairCnt k kA kB bits = PInv k kA kB bits := by
  have hnd : (List.filter (fun ij => (pairBits k (elI k ij.1) (elI k ij.2) == bits))
      (Data.pairKeys k kA kB)).Nodup := (pairKeys_nodup k kA kB).filter _
  have h1 : PairCnt k kA kB bits
      = ((Data.pairKeys k kA kB).toFinset.filter
          (fun ij => pairBits k (elI k ij.1) (elI k ij.2) = bits)).card := by
    rw [PairCnt, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hnd,
      List.toFinset_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, decide_eq_true_eq, beq_iff_eq]
  rw [h1, PInv]
  refine Finset.card_bij (fun ij _ => (elI k ij.1, elI k ij.2)) ?_ ?_ ?_
  · intro ij hij
    have hijmem : ij ∈ (Data.pairKeys k kA kB).toFinset := (Finset.mem_filter.mp hij).1
    have hbits : pairBits k (elI k ij.1) (elI k ij.2) = bits := (Finset.mem_filter.mp hij).2
    obtain ⟨hi, hj, hka, hkb⟩ := mem_pairKeys_iff.mp (List.mem_toFinset.mp hijmem)
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, hbits⟩
    · rw [hTk]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ij.1, List.mem_range.mpr hi, rfl⟩)
    · rw [hTk]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ij.2, List.mem_range.mpr hj, rfl⟩)
    · rw [← hkey ij.1 hi]; exact hka
    · rw [← hkey ij.2 hj]; exact hkb
  · intro ij₁ h₁ ij₂ h₂ heq
    have he1 : elI k ij₁.1 = elI k ij₂.1 := congrArg Prod.fst heq
    have he2 : elI k ij₁.2 = elI k ij₂.2 := congrArg Prod.snd heq
    simp only [Finset.mem_filter] at h₁ h₂
    obtain ⟨hi1, hj1, _, _⟩ := mem_pairKeys_iff.mp (List.mem_toFinset.mp h₁.1)
    obtain ⟨hi2, hj2, _, _⟩ := mem_pairKeys_iff.mp (List.mem_toFinset.mp h₂.1)
    exact Prod.ext (hinj hi1 hi2 he1) (hinj hj1 hj2 he2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hq1, hq2⟩, hqk1, hqk2, hqb⟩ := hq
    obtain ⟨i, hi, hie⟩ := mem_Tk_iff_exists k q.1 |>.mp hq1
    obtain ⟨j, hj, hje⟩ := mem_Tk_iff_exists k q.2 |>.mp hq2
    refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨List.mem_toFinset.mpr (mem_pairKeys.mpr ⟨hi, hj, ?_, ?_⟩), ?_⟩
      · rw [hkey i hi, hie]; exact hqk1
      · rw [hkey j hj, hje]; exact hqk2
      · rw [hie, hje]; exact hqb
    · exact Prod.ext hie hje

theorem pairCount_eq_PInv (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) (bits : List Bool)
    (la : List Data.PairCert) (ca : ℕ)
    (hkey : ∀ i, i < pn k → ekeyK k i = keyE k (elI k i))
    (hbit : ∀ p : Data.PairCert, p.i < pn k → p.j < pn k → Data.PairCert.chk k p = true →
      p.bits = pairBits k (elI k p.i) (elI k p.j))
    (hTk : Tk k = ((List.range (pn k)).map (elI k)).toFinset)
    (hinj : Set.InjOn (elI k) (Set.Iio (pn k)))
    (ha : Data.pairCount k kA kB bits la = some ca) :
    ca = PInv k kA kB bits := by
  rw [pairCount_eq_PairCnt k kA kB bits la ca hkey hbit ha,
    PairCnt_eq_PInv k kA kB bits hkey hTk hinj]

/-! ## 3. Invariance of `PInv` -/

theorem pairsep_pinv (k l : Fin 230) (U : IMat) (hU : IsUnit U.det)
    (kA kB : ℤ × ℤ × ℕ) (bits : List Bool)
    (hbij : ∀ A, A ∈ Tk l ↔ ∃ B ∈ Tk k, A = U * B * invMat U)
    (hk : ∀ A ∈ Tk k, keyE l (U * A * invMat U) = keyE k A)
    (hb : ∀ A ∈ Tk k, ∀ B ∈ Tk k, pairBits l (U * A * invMat U) (U * B * invMat U)
      = pairBits k A B) :
    PInv k kA kB bits = PInv l kA kB bits := by
  have hconj : ∀ X : IMat, invMat U * (U * X * invMat U) * U = X := by
    intro X
    calc invMat U * (U * X * invMat U) * U = (invMat U * U) * X * (invMat U * U) := by
          noncomm_ring
      _ = X := by rw [invMat_mul hU, one_mul, mul_one]
  have hinj : ∀ {A B : IMat}, U * A * invMat U = U * B * invMat U → A = B := by
    intro A B h
    have hh := congrArg (fun M => invMat U * M * U) h
    rwa [hconj A, hconj B] at hh
  rw [PInv, PInv]
  refine Finset.card_bij (fun p _ => (U * p.1 * invMat U, U * p.2 * invMat U)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨hp1, hp2⟩, hk1, hk2, hb1⟩ := hp
    exact ⟨⟨(hbij _).mpr ⟨p.1, hp1, rfl⟩, (hbij _).mpr ⟨p.2, hp2, rfl⟩⟩,
      by rw [hk p.1 hp1]; exact hk1,
      by rw [hk p.2 hp2]; exact hk2,
      by rw [hb p.1 hp1 p.2 hp2]; exact hb1⟩
  · intro p _ q _ hpq
    have h1 : U * p.1 * invMat U = U * q.1 * invMat U := congrArg Prod.fst hpq
    have h2 : U * p.2 * invMat U = U * q.2 * invMat U := congrArg Prod.snd hpq
    exact Prod.ext (hinj h1) (hinj h2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hq1, hq2⟩, hk1, hk2, hb1⟩ := hq
    obtain ⟨A, hA, hAeq⟩ := (hbij q.1).mp hq1
    obtain ⟨B, hB, hBeq⟩ := (hbij q.2).mp hq2
    refine ⟨(A, B), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hA, hB⟩, by rw [← hk A hA, ← hAeq]; exact hk1,
        by rw [← hk B hB, ← hBeq]; exact hk2,
        by rw [← hb A hA B hB, ← hAeq, ← hBeq]; exact hb1⟩
    · exact Prod.ext hAeq.symm hBeq.symm

end PSep

end Work.SGsep
