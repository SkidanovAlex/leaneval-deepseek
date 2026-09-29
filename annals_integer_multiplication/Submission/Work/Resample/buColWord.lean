import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buColsDefs
import Submission.Work.Resample.auMapListTail

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.Resample

open HvdH

/-! ## `Pipe` adapters for `unconsV` / `consV` -/

/-- `KernelLib.unconsV` as a `Pipe` on a one-value window. -/
theorem Pipe.unconsVbu {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog
      (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => K)) (a b : Val) :
    Pipe main prog [.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv : vs = .cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv⟩ s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv)
  have h2 := Val.cons.inj h1.1
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  rw [hout, h2.1, h2.2, h1.2]
  rfl

/-- `KernelLib.consV` as a `Pipe` on a two-value window. -/
theorem Pipe.consVbu {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
      (fun _ => K)) (a b : Val) :
    Pipe main prog [a, b] [.cons a b] K := by
  intro rest vs hvs s R hR
  have hv : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv)
  have h2 := List.cons.inj h1.2
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  rw [hout, h1.1, h2.1, h2.2]
  rfl

/-! ## The labels of one column and the per-element function -/

/-- The labels of one column: `cons (int i) (int h)` for `i < s`. -/
def buLbl (s : ℕ) (h : ℤ) : List Val :=
  (List.range s).map (fun i : ℕ => Val.cons (.int (i : ℤ)) (.int h))

/-- The function implemented by the per-column element word: `cons (int i) _ ↦ int (buWt i h)`. -/
noncomputable def buColOf (p α s t : ℕ) (h : ℤ) : Val → Val
  | .cons (.int i) _ => .int (buWt p α s t i h)
  | _ => .nil

theorem buLbl_mem {s : ℕ} {h : ℤ} {x : Val} :
    x ∈ buLbl s h ↔ ∃ i : ℕ, i < s ∧ x = Val.cons (.int (i : ℤ)) (.int h) := by
  rw [buLbl, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mpr hi, rfl⟩

theorem buLbl_length (s : ℕ) (h : ℤ) : (buLbl s h).length = s := by
  simp [buLbl]

theorem buColOf_cons (p α s t : ℕ) (h : ℤ) (i : ℤ) (v : Val) :
    buColOf p α s t h (.cons (.int i) v) = .int (buWt p α s t i h) := rfl

theorem buLbl_map (p α s t : ℕ) (h : ℤ) :
    (buLbl s h).map (buColOf p α s t h)
      = (List.range s).map (fun i : ℕ => Val.int (buWt p α s t (i : ℤ) h)) := by
  simp only [buLbl, List.map_map]
  apply List.map_congr_left
  intro i _
  exact buColOf_cons p α s t h (i : ℤ) (.int h)

theorem buCol_ofFn_range (p α s t : ℕ) (h : ℤ) :
    (List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map Val.int
      = (List.range s).map (fun i : ℕ => Val.int (buWt p α s t (i : ℤ) h)) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_ofFn, List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- `buCol` in `List.range` form. -/
theorem buCol_eq_range (p α s t : ℕ) (h : ℤ) :
    ofList ((List.range s).map (fun i : ℕ => Val.int (buWt p α s t (i : ℤ) h)))
      = buCol p α s t h := by
  show ofList ((List.range s).map (fun i : ℕ => Val.int (buWt p α s t (i : ℤ) h)))
    = ofList (List.map Val.int (List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)))
  exact congrArg ofList (buCol_ofFn_range p α s t h).symm

theorem buCol_ofList_map (p α s t : ℕ) (h : ℤ) :
    ofList ((buLbl s h).map (buColOf p α s t h)) = buCol p α s t h := by
  rw [buLbl_map, buCol_eq_range]

/-- `vsz (buCol p α s t h) ≤ (s+1)(buSZ p + 1)`. -/
theorem vsz_buCol_le {p α s t : ℕ} (h : ℤ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
    (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p) (hh : h.natAbs ≤ egM p α) :
    vsz (buCol p α s t h) ≤ (s + 1) * (buSZ p + 1) := by
  have hs0 : 0 < s := by omega
  have hsp : s < 2 ^ p := by omega
  have hα2p : α ≤ 2 ^ p := by
    have h1 : α ≤ α * α := by nlinarith [hα]
    have h3 : α ^ 2 < 2 ^ p := lt_of_lt_of_le hαp (le_of_lt (Nat.lt_two_pow_self (n := p)))
    have h2 : α * α < 2 ^ p := by simpa [pow_two] using h3
    omega
  rw [← buCol_eq_range]
  have hmem : ∀ y ∈ (List.range s).map (fun i : ℕ => Val.int (buWt p α s t (i : ℤ) h)),
      vsz y ≤ buSZ p := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [List.mem_range] at hi
    rw [Work.Fx.vsz_int]
    exact isz_buWt_le p α s t (i : ℤ) h (le_of_lt hαp) hα2p hs0 hh hsp htp hp
  have h4 := buCol_vsz_ofList_le
    (l := (List.range s).map (fun i : ℕ => Val.int (buWt p α s t (i : ℤ) h)))
    (B := buSZ p) hmem
  rw [List.length_map, List.length_range] at h4
  exact h4

/-! ## The per-column word -/

theorem buColWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (wtProg : HvdH.Cmd) (Kw : ℕ)
    (wtSpec : ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ h : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hh : h.natAbs ≤ Work.Resample.egM p α),
      ∀ rest : List HvdH.Val, HvdH.WordR main wtProg
        (fun vs => vs = [HvdH.Val.int ℓ, HvdH.Val.int h] ++ Work.Resample.buCB p α s t ++ rest)
        (fun vs out => vs = [HvdH.Val.int ℓ, HvdH.Val.int h] ++ Work.Resample.buCB p α s t ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.buWt p α s t ℓ h)] ++ Work.Resample.buCB p α s t ++ rest)
        (fun _ => Kw * (p + 1) ^ Kw)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (h : ℤ) (hh : h.natAbs ≤ Work.Resample.egM p α),
      Work.Resample.Pipe main prog (HvdH.Val.int h :: Work.Resample.buCB p α s t)
        (Work.Resample.buCol p α s t h :: Work.Resample.buCB p α s t)
        (K * (s + 1) * (p + 1) ^ K) := by
  classical
  obtain ⟨uncProg, Kuc, hUc⟩ := KL.unconsV
  obtain ⟨pickProg, Kp, hPk⟩ := KL.pick
  obtain ⟨combML, Kml, hML⟩ := MapListField.of_kernel KL
  obtain ⟨replProg, Kr, hRepl⟩ := LL.replicate
  obtain ⟨enumProg, Ke, hEnum⟩ := LL.enumerate
  refine ⟨Cmd.seq (pickProg 3) (Cmd.seq replProg (Cmd.seq enumProg
      (combML (Cmd.seq uncProg wtProg)))),
    buColK Kuc Kw Kml Kr Ke Kp, ?_⟩
  intro main p α s t hs hst hα hp htp hαp h hh
  set Λ : ℕ := buColK Kuc Kw Kml Kr Ke Kp with hΛ
  have hsp : s < 2 ^ p := by omega
  have hs0 : 0 < s := by omega
  have hb2 : 2 ≤ p + 1 := by omega
  have hmle : egM p α ≤ p + 1 := egM_le p α
  have hα2p : α < 2 ^ p := by
    have h1 : α ≤ α * α := by nlinarith [hα]
    have h3 : α ^ 2 < 2 ^ p := lt_of_lt_of_le hαp (le_of_lt (Nat.lt_two_pow_self (n := p)))
    have h2 : α * α < 2 ^ p := by simpa [pow_two] using h3
    omega
  have hszh : isz h ≤ buSZ p :=
    isz_le_buSZ_two_pow hp (le_trans hh (le_trans hmle (by
      have h2 := Nat.lt_two_pow_self (n := p); omega)))
  have hszs : isz ((s : ℤ)) ≤ buSZ p := isz_nat_le_buSZ_two_pow hp hsp
  have hszp : isz ((p : ℤ)) ≤ buSZ p := isz_nat_le_buSZ_two_pow hp (Nat.lt_two_pow_self (n := p))
  have hszα : isz ((α : ℤ)) ≤ buSZ p := isz_nat_le_buSZ_two_pow hp hα2p
  have hB4 : buSZ p + 1 ≤ (p + 1) ^ 4 := buSZ_add_one_le_four p hp
  have hBmem : ∀ v ∈ buCB p α s t, vsz v ≤ buSZ p :=
    fun v hv => vsz_buCB_le hs hst hα hp htp hαp hv
  let Bc : List Val := buCB p α s t
  let W0 : List Val := .int h :: Bc
  let W1 : List Val := .int (s : ℤ) :: W0
  let W2 : List Val := ofList (List.replicate s (Val.int h)) :: Bc
  let W3 : List Val := ofList (buLbl s h) :: Bc
  let W4 : List Val := ofList ((buLbl s h).map (buColOf p α s t h)) :: Bc
  have hmem0 : ∀ v ∈ W0, vsz v ≤ buSZ p := by
    intro v hv
    simp only [W0, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv
    · simpa only [Work.Fx.vsz_int] using hszh
    · exact hBmem v hv
  have hszl1 : Work.Fx.szl (W0.take 4) ≤ 4 * buSZ p := by
    have hsl := szl_le_len_mul (A := W0.take 4) (n := buSZ p)
      (fun v hv => hmem0 v (List.mem_of_mem_take hv))
    have hlen : (W0.take 4).length ≤ 4 := by simp [W0, Bc, buCB]
    exact le_trans hsl (Nat.mul_le_mul_right _ hlen)
  let cElem : ℕ := Kuc + Kw * (p + 1) ^ Kw
  have hElem : ∀ x ∈ buLbl s h, Pipe main (Cmd.seq uncProg wtProg) (x :: Bc)
      (buColOf p α s t h x :: Bc) cElem := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := buLbl_mem.mp hx
    have h1 : Pipe main uncProg (.cons (.int (i : ℤ)) (.int h) :: Bc)
        (.int (i : ℤ) :: .int h :: Bc) Kuc :=
      Pipe.appendTail (main := main) Bc (Pipe.unconsVbu (main := main) hUc (.int (i : ℤ)) (.int h))
    have h2 : Pipe main wtProg (.int (i : ℤ) :: .int h :: Bc)
        (.int (buWt p α s t (i : ℤ) h) :: Bc) (Kw * (p + 1) ^ Kw) := by
      intro rest0
      refine Work.Kernel.WordR_conseq
        (wtSpec main p α s t hs hst hα hp htp hαp (i : ℤ) h (by omega)
          (by exact_mod_cast hi) hh rest0)
        (fun vs hv => hv) (fun vs out hv hout => hout.2) (fun vs _ => le_rfl)
    have h12 := Pipe.comp h1 h2
    refine Pipe.le h12 ?_
    dsimp only [cElem]
    omega
  have hxbl : ∀ x ∈ buLbl s h, vsz x ≤ buLin p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := buLbl_mem.mp hx
    have hszi : isz ((i : ℤ)) ≤ buSZ p :=
      isz_nat_le_buSZ_two_pow hp (lt_of_lt_of_le hi (le_of_lt hsp))
    rw [Work.Fx.vsz_cons, Work.Fx.vsz_int, Work.Fx.vsz_int]
    simp only [buLin]
    omega
  have hybl : ∀ x ∈ buLbl s h, vsz (buColOf p α s t h x) ≤ buLin p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := buLbl_mem.mp hx
    rw [buColOf_cons, Work.Fx.vsz_int]
    have hW : isz (buWt p α s t (i : ℤ) h) ≤ buSZ p :=
      isz_buWt_le p α s t (i : ℤ) h (le_of_lt hαp) (le_of_lt hα2p) hs0 hh hsp htp hp
    simp only [buLin]
    omega
  have hstep1 : Pipe main (pickProg 3) W0 W1 (Kp * 4 * (Work.Fx.szl (W0.take 4) + 1)) :=
    Pipe.pickAt (main := main) hPk (A := W0) (k := 3) (by simp [W0, Bc, buCB])
      (v := .int (s : ℤ)) (by simp [W0, Bc, buCB])
  have hstep2 : Pipe main replProg W1 W2
      (Kr * ((s + 1) * (vsz (.int h) + 1) + isz ((s : ℤ)) + 1)) :=
    Pipe.appendTail (main := main) Bc (Pipe.replicate (main := main) hRepl (k := s) (v := .int h))
  have hstep3 : Pipe main enumProg W2 W3
      (Ke * (vsz (ofList (List.replicate s (Val.int h)))
        + (List.replicate s (Val.int h)).length
          * (((List.replicate s (Val.int h)).length).size + 1) + 1)) := by
    have hen := Pipe.appendTail (main := main) Bc
      (Pipe.enumerate (main := main) hEnum (xs := List.replicate s (Val.int h)))
    have hX : (List.range (List.replicate s (Val.int h)).length).map (fun i : ℕ =>
        Val.cons (.int (i : ℤ)) ((List.replicate s (Val.int h)).getD i .nil)) = buLbl s h := by
      rw [buLbl]
      exact enumerate_replicate s (Val.int h)
    have hw : [ofList ((List.range (List.replicate s (Val.int h)).length).map (fun i : ℕ =>
        Val.cons (.int (i : ℤ)) ((List.replicate s (Val.int h)).getD i .nil)))] ++ Bc = W3 := by
      show ofList ((List.range (List.replicate s (Val.int h)).length).map (fun i : ℕ =>
        Val.cons (.int (i : ℤ)) ((List.replicate s (Val.int h)).getD i .nil))) :: Bc = W3
      rw [hX]
    exact Pipe.rw hen hw
  have hstep4 : Pipe main (combML (Cmd.seq uncProg wtProg)) W3 W4
      ((buLbl s h).length * (cElem + Kml * (buLin p + 1)) + Kml) :=
    auMapListTail (main := main) (q := Cmd.seq uncProg wtProg) (T := Bc)
      (xs := buLbl s h) (F := buColOf p α s t h) (c := cElem) (L := buLin p)
      hML hElem hxbl hybl
  -- cost closing
  have hb2' : 2 ≤ p + 1 := by omega
  have hBp : buSZ p + 1 ≤ (p + 1) ^ 4 := buSZ_add_one_le_four p hp
  have hΛ30 : 30 ≤ Λ := by rw [hΛ]; simp only [buColK]; omega
  have hc1 : Kp * 4 * (Work.Fx.szl (W0.take 4) + 1) ≤ 20 * ((s + 1) * (p + 1) ^ Λ) := by
    have h1 : 4 * (Work.Fx.szl (W0.take 4) + 1) ≤ 20 * (p + 1) ^ 4 := by
      have h2 : Work.Fx.szl (W0.take 4) ≤ 4 * buSZ p := hszl1
      nlinarith [h2, hBp]
    calc Kp * 4 * (Work.Fx.szl (W0.take 4) + 1)
        = Kp * (4 * (Work.Fx.szl (W0.take 4) + 1)) := by ring
      _ ≤ (p + 1) ^ Kp * (20 * (p + 1) ^ 4) :=
            Nat.mul_le_mul (le_pow_self (p + 1) Kp hb2') h1
      _ = 20 * (p + 1) ^ (Kp + 4) := by rw [pow_add]; ring
      _ ≤ 20 * (p + 1) ^ Λ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
            (by rw [hΛ]; simp only [buColK]; omega))
      _ ≤ 20 * ((s + 1) * (p + 1) ^ Λ) :=
            Nat.mul_le_mul_left _ (le_mul_succ s ((p + 1) ^ Λ))
  have hc2 : Kr * ((s + 1) * (vsz (.int h) + 1) + isz ((s : ℤ)) + 1)
      ≤ 3 * ((s + 1) * (p + 1) ^ Λ) := by
    have h1 : (s + 1) * (vsz (.int h) + 1) + isz ((s : ℤ)) + 1 ≤ 3 * ((s + 1) * (p + 1) ^ 4) := by
      have hh1 : vsz (.int h) + 1 ≤ buSZ p + 1 := by rw [Work.Fx.vsz_int]; omega
      have hs1 : isz ((s : ℤ)) + 1 ≤ buSZ p + 1 := by omega
      have ha : (s + 1) * (vsz (.int h) + 1) ≤ (s + 1) * (buSZ p + 1) :=
        Nat.mul_le_mul_left _ hh1
      have hb : isz ((s : ℤ)) + 1 ≤ (s + 1) * (buSZ p + 1) :=
        le_trans hs1 (le_mul_succ s (buSZ p + 1))
      have h3 : (s + 1) * (buSZ p + 1) ≤ (s + 1) * (p + 1) ^ 4 :=
        Nat.mul_le_mul_left _ hBp
      linarith [ha, hb, h3]
    calc Kr * ((s + 1) * (vsz (.int h) + 1) + isz ((s : ℤ)) + 1)
        ≤ (p + 1) ^ Kr * (3 * ((s + 1) * (p + 1) ^ 4)) :=
            Nat.mul_le_mul (le_pow_self (p + 1) Kr hb2') h1
      _ = 3 * (s + 1) * (p + 1) ^ (Kr + 4) := by rw [pow_add]; ring
      _ ≤ 3 * (s + 1) * (p + 1) ^ Λ :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
              (by rw [hΛ]; simp only [buColK]; omega))
      _ = 3 * ((s + 1) * (p + 1) ^ Λ) := by ring
  have hc3 : Ke * (vsz (ofList (List.replicate s (Val.int h)))
        + (List.replicate s (Val.int h)).length
          * (((List.replicate s (Val.int h)).length).size + 1) + 1)
      ≤ 3 * ((s + 1) * (p + 1) ^ Λ) := by
    rw [List.length_replicate]
    have h1 : vsz (ofList (List.replicate s (Val.int h))) + s * (s.size + 1) + 1
        ≤ 3 * ((s + 1) * (p + 1) ^ 4) := by
      have hvsz : vsz (ofList (List.replicate s (Val.int h))) ≤ (s + 1) * (vsz (.int h) + 1) := by
        have hvl := buCol_vsz_ofList_le (l := List.replicate s (Val.int h)) (B := vsz (.int h))
          (fun x hx => le_of_eq (by rw [List.eq_of_mem_replicate hx]))
        rwa [List.length_replicate] at hvl
      have hh1 : vsz (.int h) + 1 ≤ buSZ p + 1 := by rw [Work.Fx.vsz_int]; omega
      have hs1 : s.size + 1 ≤ buSZ p + 1 := by
        have h2 : s.size ≤ p := Nat.size_le.mpr hsp
        simp only [buSZ]; omega
      have h1' : vsz (ofList (List.replicate s (Val.int h))) ≤ (s + 1) * (buSZ p + 1) :=
        le_trans hvsz (Nat.mul_le_mul_left _ hh1)
      have h2' : s * (s.size + 1) ≤ (s + 1) * (buSZ p + 1) :=
        le_trans (Nat.mul_le_mul_left _ hs1) (Nat.mul_le_mul_right _ (by omega))
      have h3' : (1 : ℕ) ≤ (s + 1) * (buSZ p + 1) := by
        have h5 : 1 ≤ buSZ p + 1 := by have := buSZ_ge p; omega
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h4 : (s + 1) * (buSZ p + 1) ≤ (s + 1) * (p + 1) ^ 4 := Nat.mul_le_mul_left _ hBp
      linarith [h1', h2', h3', h4]
    calc Ke * (vsz (ofList (List.replicate s (Val.int h))) + s * (s.size + 1) + 1)
        ≤ (p + 1) ^ Ke * (3 * ((s + 1) * (p + 1) ^ 4)) :=
            Nat.mul_le_mul (le_pow_self (p + 1) Ke hb2') h1
      _ = 3 * (s + 1) * (p + 1) ^ (Ke + 4) := by rw [pow_add]; ring
      _ ≤ 3 * (s + 1) * (p + 1) ^ Λ :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
              (by rw [hΛ]; simp only [buColK]; omega))
      _ = 3 * ((s + 1) * (p + 1) ^ Λ) := by ring
  have hc4 : (buLbl s h).length * (cElem + Kml * (buLin p + 1)) + Kml
      ≤ 4 * ((s + 1) * (p + 1) ^ Λ) := by
    rw [buLbl_length]
    have hΛKml' : Kml ≤ Λ := by rw [hΛ]; simp only [buColK]; omega
    have hA : cElem + Kml * (buLin p + 1) ≤ 3 * (p + 1) ^ Λ := by
      dsimp only [cElem]
      have h1 : Kuc ≤ (p + 1) ^ Λ :=
        le_trans (le_pow_self (p + 1) Kuc hb2')
          (Nat.pow_le_pow_right (by omega) (by rw [hΛ]; simp only [buColK]; omega))
      have h2 : Kw * (p + 1) ^ Kw ≤ (p + 1) ^ Λ :=
        le_trans (const_mul_pow_le_pow (C := Kw) (b := p + 1) (n := Kw) hb2')
          (Nat.pow_le_pow_right (by omega) (by rw [hΛ]; simp only [buColK]; omega))
      have h3 : Kml * (buLin p + 1) ≤ (p + 1) ^ Λ := by
        have hlin : buLin p + 1 ≤ (p + 1) ^ 5 := by
          have h4 : buLin p + 1 ≤ 3 * (buSZ p + 1) := by
            have hb := buSZ_ge p
            simp only [buLin]
            omega
          calc buLin p + 1 ≤ 3 * (buSZ p + 1) := h4
            _ ≤ 3 * (p + 1) ^ 4 := Nat.mul_le_mul_left 3 hBp
            _ ≤ (p + 1) ^ 5 := by
                calc 3 * (p + 1) ^ 4 = (p + 1) ^ 4 * 3 := by ring
                  _ ≤ (p + 1) ^ 4 * (p + 1) := Nat.mul_le_mul_left _ (by omega)
                  _ = (p + 1) ^ 5 := by ring
        calc Kml * (buLin p + 1) ≤ Kml * (p + 1) ^ 5 := Nat.mul_le_mul_left _ hlin
          _ ≤ (p + 1) ^ (Kml + 5) := const_mul_pow_le_pow (C := Kml) (b := p + 1) (n := 5) hb2'
          _ ≤ (p + 1) ^ Λ := Nat.pow_le_pow_right (by omega)
              (by rw [hΛ]; simp only [buColK]; omega)
      linarith [h1, h2, h3]
    have hKml : Kml ≤ (p + 1) ^ Λ :=
      le_trans (le_pow_self (p + 1) Kml hb2')
        (Nat.pow_le_pow_right (by omega) hΛKml')
    calc s * (cElem + Kml * (buLin p + 1)) + Kml
        ≤ s * (3 * (p + 1) ^ Λ) + (p + 1) ^ Λ :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hA) hKml
      _ = (3 * s + 1) * (p + 1) ^ Λ := by ring
      _ ≤ 4 * (s + 1) * (p + 1) ^ Λ := by
          have h6 : 3 * s + 1 ≤ 4 * (s + 1) := by omega
          calc (3 * s + 1) * (p + 1) ^ Λ ≤ (4 * (s + 1)) * (p + 1) ^ Λ :=
                Nat.mul_le_mul_right _ h6
            _ = 4 * (s + 1) * (p + 1) ^ Λ := by ring
      _ = 4 * ((s + 1) * (p + 1) ^ Λ) := by ring
  have htot : Kp * 4 * (Work.Fx.szl (W0.take 4) + 1)
      + (Kr * ((s + 1) * (vsz (.int h) + 1) + isz ((s : ℤ)) + 1)
        + (Ke * (vsz (ofList (List.replicate s (Val.int h)))
            + (List.replicate s (Val.int h)).length
              * (((List.replicate s (Val.int h)).length).size + 1) + 1)
          + ((buLbl s h).length * (cElem + Kml * (buLin p + 1)) + Kml)))
      ≤ Λ * (s + 1) * (p + 1) ^ Λ := by
    have h30 : Kp * 4 * (Work.Fx.szl (W0.take 4) + 1)
        + (Kr * ((s + 1) * (vsz (.int h) + 1) + isz ((s : ℤ)) + 1)
          + (Ke * (vsz (ofList (List.replicate s (Val.int h)))
              + (List.replicate s (Val.int h)).length
                * (((List.replicate s (Val.int h)).length).size + 1) + 1)
            + ((buLbl s h).length * (cElem + Kml * (buLin p + 1)) + Kml)))
        ≤ 30 * ((s + 1) * (p + 1) ^ Λ) := by
      linarith [hc1, hc2, hc3, hc4]
    calc _ ≤ 30 * ((s + 1) * (p + 1) ^ Λ) := h30
      _ ≤ Λ * ((s + 1) * (p + 1) ^ Λ) := Nat.mul_le_mul_right _ hΛ30
      _ = Λ * (s + 1) * (p + 1) ^ Λ := by ring
  intro rest0
  have g1 : WordR main (pickProg 3) (fun vs => vs = W0 ++ rest0) (fun _ out => out = W1 ++ rest0)
      (fun _ => Kp * 4 * (Work.Fx.szl (W0.take 4) + 1)) := hstep1 rest0
  have g2 : WordR main replProg (fun vs => vs = W1 ++ rest0) (fun _ out => out = W2 ++ rest0)
      (fun _ => Kr * ((s + 1) * (vsz (.int h) + 1) + isz ((s : ℤ)) + 1)) := hstep2 rest0
  have g3 : WordR main enumProg (fun vs => vs = W2 ++ rest0) (fun _ out => out = W3 ++ rest0)
      (fun _ => Ke * (vsz (ofList (List.replicate s (Val.int h)))
        + (List.replicate s (Val.int h)).length
          * (((List.replicate s (Val.int h)).length).size + 1) + 1)) :=
    hstep3 rest0
  have g4 : WordR main (combML (Cmd.seq uncProg wtProg))
      (fun vs => vs = W3 ++ rest0) (fun _ out => out = W4 ++ rest0)
      (fun _ => (buLbl s h).length * (cElem + Kml * (buLin p + 1)) + Kml) := hstep4 rest0
  have gtot := buCol_comp g1 (buCol_comp g2 (buCol_comp g3 g4))
  refine Work.Kernel.WordR_conseq gtot ?_ ?_ ?_
  · intro vs hvs
    dsimp only [W0, Bc] at hvs ⊢
    exact hvs
  · intro vs out hvs hout
    rw [hout]
    dsimp only [W4, Bc]
    rw [buCol_ofList_map]
  · intro vs _
    exact htot

end Work.Resample
