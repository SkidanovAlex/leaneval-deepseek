import Submission.ZagierHoffmanProof.StepL23
import Submission.ZagierHoffmanProof.Counting

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L24: leading-tuple value through the prefix prepends

The (2.14) chain prepends the prefix entries `(s_{j-1},…,s_1)` to every tuple of
the B*_{s_j}-output.  These lemmas record the values of the prefixed tuples at
Nat positions: in the front region (position `m < xs.length`) the value is the
front list entry `xs.reverse` at `m`, in the base region it is the original
tuple at `m − xs.length`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma consVec_val (x : ℕ+) {m : ℕ} (t : Fin m → ℕ+) :
    ∀ j : Fin (m + 1),
      (consVec x t) j = if hz : (j : ℕ) = 0 then x else t ⟨(j : ℕ) - 1, by omega⟩ := by
  classical
  intro j
  by_cases hz : (j : ℕ) = 0
  · have hj0 : j = ⟨0, (by omega : 0 < m + 1)⟩ := Fin.ext (by simpa using hz)
    rw [hj0]
    rw [consVec_zero x t]
    simp
  · let i : Fin m := ⟨(j : ℕ) - 1, by
      have hlt : (j : ℕ) < m + 1 := j.isLt
      omega⟩
    have hj : j = ⟨(i : ℕ) + 1, by omega⟩ := by
      apply Fin.ext
      simp [i]
      omega
    rw [hj]
    rw [consVec_succ x t i]
    simp [i, hz]

/-- Base-region values of the prefixed tuple: at position `m ≥ xs.length` the value is
the original tuple entry at `m − xs.length`. -/
lemma prependList_c_base_value {ι : Type} [Fintype ι] (R : FixedOver F ι) :
    ∀ (xs : List ℕ+) (i : ι) (m : ℕ)
      (hm : m < (FixedOver.prependList F R xs).dep i) (hge : xs.length ≤ m),
      (FixedOver.prependList F R xs).c i ⟨m, hm⟩ =
        (R.c i) ⟨m - xs.length, by
          have hd := FixedOver.prependList_dep F R xs i
          rw [hd] at hm
          omega⟩ := by
  classical
  intro xs
  induction xs generalizing R with
  | nil =>
      intro i m hm hge
      change (R.c i) ⟨m, hm⟩ = (R.c i) ⟨m - 0, by
          have hd := FixedOver.prependList_dep F R [] i
          rw [hd] at hm
          omega⟩
      congr 1
  | cons x xs' ih =>
      intro i m hm hge
      change m < (FixedOver.prependList F (FixedOver.prepend F R x) xs').dep i at hm
      have hll : (x :: xs').length = xs'.length + 1 := by simp
      have hge1 : xs'.length ≤ m := by omega
      calc
        (FixedOver.prependList F R (x :: xs')).c i ⟨m, hm⟩
            = (FixedOver.prependList F (FixedOver.prepend F R x) xs').c i ⟨m, hm⟩ := by rfl
        _ = (FixedOver.prepend F R x).c i ⟨m - xs'.length, _⟩ :=
              ih (FixedOver.prepend F R x) i m hm hge1
        _ = (R.c i) ⟨m - (x :: xs').length, _⟩ := by
              -- (prepend R x).c i = consVec x (R.c i) at index m − xs'.length (≥ 1)
              change (consVec x (R.c i)) ⟨m - xs'.length, _⟩ = (R.c i) ⟨m - (x :: xs').length, _⟩
              have hcv := consVec_val x (R.c i) ⟨m - xs'.length, by
                have hd : (FixedOver.prependList F (FixedOver.prepend F R x) xs').dep i =
                    (FixedOver.prepend F R x).dep i + xs'.length := FixedOver.prependList_dep F (FixedOver.prepend F R x) xs' i
                have hlt : m < (FixedOver.prepend F R x).dep i + xs'.length := by simpa [hd] using hm
                have hd1 : (FixedOver.prepend F R x).dep i = R.dep i + 1 := by rfl
                omega⟩
              rw [hcv]
              have hnz : m - xs'.length ≠ 0 := by omega
              simp [hnz]
              congr 1

/-- Front-region values of the prefixed tuple: at position `m < xs.length` the value
is the front entry (`xs.reverse` at `m`). -/
lemma prependList_c_front_value {ι : Type} [Fintype ι] (R : FixedOver F ι) :
    ∀ (xs : List ℕ+) (i : ι) (m : ℕ)
      (hm : m < (FixedOver.prependList F R xs).dep i) (hmf : m < xs.length),
      (FixedOver.prependList F R xs).c i ⟨m, hm⟩ =
        (xs.reverse.get ⟨m, by simpa using hmf⟩ : ℕ+) := by
  classical
  intro xs
  induction xs generalizing R with
  | nil =>
      intro i m hm hmf
      simp at hmf
  | cons x xs' ih =>
      intro i m hm hmf
      change m < (FixedOver.prependList F (FixedOver.prepend F R x) xs').dep i at hm
      have hll : (x :: xs').length = xs'.length + 1 := by simp
      by_cases hp : m < xs'.length
      · calc
          (FixedOver.prependList F R (x :: xs')).c i ⟨m, hm⟩
              = (FixedOver.prependList F (FixedOver.prepend F R x) xs').c i ⟨m, hm⟩ := by rfl
          _ = (xs'.reverse.get ⟨m, by simpa using hp⟩ : ℕ+) :=
                ih (FixedOver.prepend F R x) i m hm hp
          _ = ((x :: xs').reverse.get ⟨m, by simpa using hmf⟩ : ℕ+) := by
                rw [List.get_eq_getElem]
                rw [List.get_eq_getElem]
                simp
                rw [List.getElem_append_left (by simpa using hp : m < (xs'.reverse).length)]
                simp
      · have hge : xs'.length ≤ m := le_of_not_gt hp
        have hm0 : m = xs'.length := by omega
        subst m
        calc
          (FixedOver.prependList F R (x :: xs')).c i ⟨xs'.length, hm⟩
              = (FixedOver.prependList F (FixedOver.prepend F R x) xs').c i ⟨xs'.length, hm⟩ := by rfl
          _ = (FixedOver.prepend F R x).c i ⟨xs'.length - xs'.length, _⟩ :=
                prependList_c_base_value F (FixedOver.prepend F R x) xs' i xs'.length hm (by omega)
          _ = x := by
                change (consVec x (R.c i)) ⟨xs'.length - xs'.length, _⟩ = x
                have h0 : (⟨xs'.length - xs'.length, (by omega)⟩ : Fin (R.dep i + 1)) = ⟨0, by omega⟩ := by
                  apply Fin.ext
                  simp
                rw [h0]
                exact consVec_zero x (R.c i)
          _ = ((x :: xs').reverse.get ⟨xs'.length, by simpa using hmf⟩ : ℕ+) := by
                rw [List.get_eq_getElem]
                simp

/-- Value of the B*_{s_j} leading tuple at every position ℓ = s⟨(j−1)+ℓ⟩. -/
lemma Bs_leading_pos (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdep0 : R0.depA u = (r - k) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    ∀ (ℓ : ℕ) (hℓ : ℓ < Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) u)))
      (hbd : (j - 1) + ℓ < r),
      Bs.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) u)) ⟨ℓ, hℓ⟩ =
        s ⟨(j - 1) + ℓ, hbd⟩ := by
  classical
  intro D Bs ℓ hℓ hbd
  let u' := RelData.iterIdx F (k - j - 1) (toData F R0) u
  let n := k - j - 1
  let v := s ⟨j - 1, by omega⟩
  have hdepBs : Bs.dep (Sum.inl u') = (RelData.BCqIter F n (toData F R0)).depA u' + 1 := by
    dsimp [Bs, ofBstarOver, D, n]
  have hdepD : (RelData.BCqIter F n (toData F R0)).depA u' = R0.depA u + n := by
    exact RelData.BCqIter_depA_at F n (toData F R0) u
  have hcBs : Bs.c (Sum.inl u') = consVec v ((RelData.BCqIter F n (toData F R0)).cA u') := by
    dsimp [Bs, ofBstarOver, v, n]
  rw [hcBs]
  change consVec v ((RelData.BCqIter F n (toData F R0)).cA u') ⟨ℓ, hℓ⟩ =
      s ⟨(j - 1) + ℓ, hbd⟩
  by_cases hz : ℓ = 0
  · subst ℓ
    change consVec v ((RelData.BCqIter F n (toData F R0)).cA u') ⟨0, hℓ⟩ =
        s ⟨(j - 1) + 0, hbd⟩
    have hidx0 : (⟨0, hℓ⟩ : Fin ((RelData.BCqIter F n (toData F R0)).depA u' + 1)) =
        ⟨0, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hidx0]
    rw [consVec_zero]
    change s ⟨j - 1, by omega⟩ = s ⟨(j - 1) + 0, hbd⟩
    congr 1
  · have hℓnz : ℓ ≠ 0 := hz
    have hbv : ℓ - 1 < (RelData.BCqIter F n (toData F R0)).depA u' := by
      have hℓ' : ℓ < Bs.dep (Sum.inl u') := hℓ
      rw [hdepBs] at hℓ'
      have hpos : 0 < ℓ := Nat.pos_of_ne_zero hℓnz
      omega
    -- peel the consVec at position ℓ = (ℓ−1)+1
    let i : Fin ((RelData.BCqIter F n (toData F R0)).depA u') := ⟨ℓ - 1, hbv⟩
    have hℓi : (⟨ℓ, hℓ⟩ : Fin ((RelData.BCqIter F n (toData F R0)).depA u' + 1)) =
        ⟨(i : ℕ) + 1, by omega⟩ := by
      apply Fin.ext
      simp [i]
      omega
    rw [hℓi]
    rw [consVec_succ v ((RelData.BCqIter F n (toData F R0)).cA u') i]
    change (RelData.BCqIter F n (toData F R0)).cA u' ⟨ℓ - 1, hbv⟩ =
      s ⟨(j - 1) + ℓ, hbd⟩
    -- value of the BC_q-iterate at ℓ−1
    have hbv' : ℓ - 1 < R0.depA u + n := by
      simpa [hdepD] using hbv
    have hvD := RelData.BCqIter_cA_value F n (toData F R0) u ⟨ℓ - 1, hbv'⟩
    have hidxD : (⟨ℓ - 1, hbv⟩ : Fin ((RelData.BCqIter F n (toData F R0)).depA u')) =
        Fin.cast (RelData.BCqIter_depA_at F n (toData F R0) u).symm ⟨ℓ - 1, hbv'⟩ := by
      apply Fin.ext
      simp
    rw [hidxD]
    rw [hvD]
    by_cases hq : ℓ - 1 < n
    · -- q-region: value qExp = q = s⟨(j−1)+ℓ⟩ (hmid)
      have hq' : (((⟨ℓ - 1, hbv'⟩ : Fin (R0.depA u + n)) : ℕ)) < n := by simpa using hq
      rw [dif_pos hq']
      change qExp F = s ⟨(j - 1) + ℓ, hbd⟩
      apply Subtype.ext
      change Nat.card F = (s ⟨(j - 1) + ℓ, hbd⟩ : ℕ)
      have hge : (j : ℕ) ≤ (j - 1) + ℓ := by omega
      have hltk : (j - 1) + ℓ < k - 1 := by
        have hq1 : ℓ - 1 < k - j - 1 := hq
        omega
      have hm := hmid ⟨(j - 1) + ℓ, hbd⟩ hge hltk
      exact hm.symm
    · -- tail region: value = R0.cA u at (ℓ−1) − n
      have hge : n ≤ ℓ - 1 := le_of_not_gt hq
      simp [hq]
      have hy : (ℓ - 1) - n < R0.depA u := by
        have hlt : ℓ - 1 < R0.depA u + n := hbv'
        omega
      change (R0.cA u) ⟨(ℓ - 1) - n, hy⟩ = s ⟨(j - 1) + ℓ, hbd⟩
      -- value = bstarBase at (ℓ−1)−n, via hc0 transport
      have hyy : ((⟨(ℓ - 1) - n, hy⟩ : Fin (R0.depA u)) : ℕ) = (ℓ - 1) - n := by rfl
      have hc0' := congrFun (hc0 hdep0) (Fin.cast hdep0 ⟨(ℓ - 1) - n, hy⟩)
      have hcastv : (Fin.cast hdep0.symm (Fin.cast hdep0 ⟨(ℓ - 1) - n, hy⟩) : Fin (R0.depA u)) =
          ⟨(ℓ - 1) - n, hy⟩ := by
        apply Fin.ext
        simp
      rw [hcastv] at hc0'
      -- hc0' : R0.cA u ⟨(ℓ−1)−n, hy⟩ = bstarBase F r s k hk1 hkr hbig (Fin.cast hdep0 ⟨(ℓ−1)−n, hy⟩)
      rw [hc0']
      -- value of bstarBase at (ℓ−1)−n : s⟨k−1 + ((ℓ−1)−n)⟩
      have hbb : bstarBase F r s k hk1 hkr hbig (Fin.cast hdep0 ⟨(ℓ - 1) - n, hy⟩) =
          s ⟨k - 1 + ((ℓ - 1) - n), by
            have hlt : (ℓ - 1) - n < (r - k) + 1 := by
              have hlt0 : (ℓ - 1) - n < R0.depA u := hy
              simpa [hdep0] using hlt0
            omega⟩ := by
        by_cases hy0 : (ℓ - 1) - n = 0
        · have hcast0 : Fin.cast hdep0 ⟨(ℓ - 1) - n, hy⟩ = ⟨0, by
            have hlt : 0 < (r - k) + 1 := by omega
            omega⟩ := by
            apply Fin.ext
            simpa using hy0
          rw [hcast0]
          have hh := bstarBase_head F r s k hk1 hkr hbig
          simpa [hy0] using hh
        · have hyge : 0 < (ℓ - 1) - n := Nat.pos_of_ne_zero hy0
          let y : Fin (r - k) := ⟨(ℓ - 1) - n - 1, by
            have hlt0 : (ℓ - 1) - n < (r - k) + 1 := by
              have hlt1 : (ℓ - 1) - n < R0.depA u := hy
              simpa [hdep0] using hlt1
            omega⟩
          have hcast1 : Fin.cast hdep0 ⟨(ℓ - 1) - n, hy⟩ = ⟨(y : ℕ) + 1, by
            have hlt0 : (ℓ - 1) - n < (r - k) + 1 := by
              have hlt1 : (ℓ - 1) - n < R0.depA u := hy
              simpa [hdep0] using hlt1
            omega⟩ := by
            apply Fin.ext
            simp [y]
            omega
          rw [hcast1]
          have ht := bstarBase_tail F r s k hk1 hkr hbig y
          rw [ht]
          change s ⟨k + (y : ℕ), by omega⟩ = s ⟨k - 1 + ((ℓ - 1) - n), by
            have hlt : (ℓ - 1) - n < (r - k) + 1 := by
              have hlt0 : (ℓ - 1) - n < R0.depA u := hy
              simpa [hdep0] using hlt0
            omega⟩
          congr 1
          apply Fin.ext
          simp [y]
          omega
      rw [hbb]
      -- target: s⟨k−1+((ℓ−1)−n)⟩ = s⟨(j−1)+ℓ⟩ : same index value
      congr 1
      apply Fin.ext
      simp
      omega

lemma sPrefix_reverse_value (r : ℕ) (s : Fin r → ℕ+) (j : ℕ) (hr1 : 1 ≤ r) (hj : j ≤ r)
    (m : ℕ) (hm : m < (sPrefix r s j hr1 hj).length) :
    (sPrefix r s j hr1 hj).reverse.get ⟨m, by simpa using hm⟩ = s ⟨m, by
      have hlen : (sPrefix r s j hr1 hj).length = j - 1 := sPrefix_length r s j hr1 hj
      have hm' : m < j - 1 := by simpa [hlen] using hm
      omega⟩ := by
  classical
  have hmjl : m < j - 1 := by
    have hlen : (sPrefix r s j hr1 hj).length = j - 1 := sPrefix_length r s j hr1 hj
    simpa [hlen] using hm
  rw [List.get_eq_getElem]
  simp [sPrefix, List.getElem_reverse, List.getElem_map, List.getElem_range]
  congr 1
  apply Fin.ext
  simp
  omega

lemma leading_tuple_value (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdep0 : R0.depA u = (r - k) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ (m : ℕ) (hmQ : m < Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) u)))
      (hmr : m < r),
      Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) u)) ⟨m, hmQ⟩ = s ⟨m, hmr⟩ := by
  classical
  intro D Bs Q m hmQ hmr
  let u' := RelData.iterIdx F (k - j - 1) (toData F R0) u
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  by_cases hpre : m < (sPrefix r s j (by omega) (by omega)).length
  · -- front region: value = (sPrefix.reverse).get m = s⟨m⟩
    have hval := prependList_c_front_value F Bs (sPrefix r s j (by omega) (by omega))
      (Sum.inl u') m hmQ hpre
    rw [hval]
    exact sPrefix_reverse_value r s j (by omega) (by omega) m hpre
  · -- base region: value = Bs.c u' at m − len
    have hge : (sPrefix r s j (by omega) (by omega)).length ≤ m := le_of_not_gt hpre
    have hval := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
      (Sum.inl u') m hmQ hge
    rw [hval]
    have hQdep : Q.dep (Sum.inl u') =
        Bs.dep (Sum.inl u') + (sPrefix r s j (by omega) (by omega)).length := by
      exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl u')
    have hm1 : m < Bs.dep (Sum.inl u') + (sPrefix r s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hmQ
    have hℓ : m - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inl u') := by
      omega
    have hbd' : (j - 1) + (m - (sPrefix r s j (by omega) (by omega)).length) < r := by
      omega
    have hbv := Bs_leading_pos F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 u hdep0 hc0 hbhd
      (m - (sPrefix r s j (by omega) (by omega)).length) hℓ hbd'
    rw [hbv]
    congr 1
    apply Fin.ext
    simp
    omega

/-- Depth of the leading member of the (2.14) chain is `r`. -/
lemma leading_dep (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdep0 : R0.depA u = (r - k) + 1)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) u)) = r := by
  classical
  intro D Bs Q
  let u' := RelData.iterIdx F (k - j - 1) (toData F R0) u
  have h1 := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl u')
  -- h1 : Q.dep u' = Bs.dep u' + (sPrefix…).length
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 := sPrefix_length r s j (by omega) (by omega)
  have h2 : Bs.dep (Sum.inl u') = (RelData.BCqIter F (k - j - 1) (toData F R0)).depA u' + 1 := by
    dsimp [Bs, ofBstarOver, D]
  have h3 : (RelData.BCqIter F (k - j - 1) (toData F R0)).depA u' = R0.depA u + (k - j - 1) := by
    dsimp [u']
    exact RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) u
  calc
    Q.dep (Sum.inl u') = Bs.dep (Sum.inl u') + (sPrefix r s j (by omega) (by omega)).length := h1
    _ = Bs.dep (Sum.inl u') + (j - 1) := by rw [hlen]
    _ = ((RelData.BCqIter F (k - j - 1) (toData F R0)).depA u' + 1) + (j - 1) := by rw [h2]
    _ = (R0.depA u + (k - j - 1) + 1) + (j - 1) := by rw [h3]
    _ = r := by omega

/-- The leading member of the (2.14) chain evaluates to ζ_A(s). -/
theorem leading_zeta (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdep0 : R0.depA u = (r - k) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ζ_A F s = ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) u))) := by
  classical
  intro D Bs Q
  let u' := RelData.iterIdx F (k - j - 1) (toData F R0) u
  have hdepQ : Q.dep (Sum.inl u') = r := by
    dsimp [Q, Bs, D, u']
    exact leading_dep F r s k j hk1 hkr hj1 hjk hbig hsj R0 u hdep0 hbhd
  -- value equality at every position of the `Q.dep u'`-domain
  exact (ζ_A_eq_of_reindex F hdepQ (Q.c (Sum.inl u')) s
    (fun i : Fin (Q.dep (Sum.inl u')) => by
      have hmr : (i : ℕ) < r := by
        have hq := i.isLt
        simpa [hdepQ] using hq
      have hv := leading_tuple_value F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 u hdep0 hc0 hbhd
        (i : ℕ) i.isLt hmr
      rw [hv])).symm

end ZagierHoffmanPositiveChar
