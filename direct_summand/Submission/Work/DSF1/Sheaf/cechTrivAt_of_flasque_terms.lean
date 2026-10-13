import Mathlib
import Submission.Work.DSF1.Sheaf.FHCCDesign
import Submission.Work.DSF1.Sheaf.FlasqueDevissage

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ## The dévissage

The complex of sections of a flasque augmented complex is exact in positive degrees on
opens contained in `V`.  The proof is the usual dévissage along the syzygies:

* `CyclesFlasque K d V n` says that the presheaf of `n`-cycles has surjective restriction
  maps between opens contained in `V`;
* `CyclesFlasque 0` follows from the exactness `ker (d 0) = im aug` together with flasqueness
  of `F` (`cyclesFlasque_zero_aux`);
* if `CyclesFlasque n` holds, every cocycle of `K (n+1)` over `W ≤ V` is a coboundary over `W`
  (`exactAt_of_cyclesFlasque`): one covers `W` by finitely many opens on which the cocycle is a
  coboundary, and glues the local primitive up to an extension of the discrepancy, which lives
  in the flasque sheaf of `n`-cycles;
* `CyclesFlasque (n+1)` then follows by extending a primitive of a cycle over `W'` to `W`,
  using flasqueness of `K n`.
-/

/-! ### Cycles of degree zero -/

/-- `CyclesFlasque K d V 0`: a `0`-cycle over `W' ≤ V` is in the image of the augmentation
(by `hexact0`); a preimage in `F` extends to `W` because `F` is flasque. -/
lemma cyclesFlasque_zero_aux
    (K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (d : ∀ n : ℕ, K n ⟶ K (n+1))
    (F : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (aug : F ⟶ K 0) (V : X.Opens)
    (hF : TopCat.Presheaf.IsFlasque F)
    (hzero : CategoryStruct.comp aug (d 0) = 0)
    (hexact0 : ∀ (W : X.Opens), W ≤ V → ∀ x : (K 0).obj (op W),
      ((d 0).app (op W) x = 0 ↔
        ∃ y : (F.obj (op W)), (aug.app (op W)) y = x)) :
    CyclesFlasque K d V 0 := by
  intro W' W h hWV z hz
  have hW'V : W' ≤ V := h.trans hWV
  obtain ⟨y, hy⟩ := (hexact0 W' hW'V z).mp hz
  have hEpi : Epi (F.map (homOfLE h).op) := hF.epi (homOfLE h).op
  obtain ⟨y', hy'⟩ := (AddCommGrpCat.epi_iff_surjective (F.map (homOfLE h).op)).mp hEpi y
  refine ⟨(aug.app (op W)) y', ?_, ?_⟩
  · have h0 := congrArg (fun (f : F ⟶ K 1) => f.app (op W) y') hzero
    simpa using h0
  · have hnat := aug_naturality aug (A := W) (B := W') h y'
    rw [← hnat, hy', hy]

/-! ### Gluing and separating over a cover by two opens -/

/-- `resEq` commutes with the canonical identification `A ⊓ B ≅ B ⊓ A` (first projection). -/
lemma res_inf_comm {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})} {A B : X.Opens}
    (x : P.obj (op A)) :
    resEq P (inf_comm A B) (P.map (Opens.infLELeft A B).op x) =
      P.map (Opens.infLERight B A).op x := by
  rw [resEq]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

/-- `resEq` commutes with the canonical identification `A ⊓ B ≅ B ⊓ A` (second projection). -/
lemma res_inf_comm' {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})} {A B : X.Opens}
    (y : P.obj (op B)) :
    resEq P (inf_comm A B) (P.map (Opens.infLERight A B).op y) =
      P.map (Opens.infLELeft B A).op y := by
  rw [resEq]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

/-- Separation for a cover by two opens. -/
lemma sheaf_sep_pair {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (hP : TopCat.Presheaf.IsSheaf P) {A B C : X.Opens}
    (hAC : A ≤ C) (hBC : B ≤ C) (hcov : C ≤ A ⊔ B) {s t : P.obj (op C)}
    (hA : P.map (homOfLE hAC).op s = P.map (homOfLE hAC).op t)
    (hB : P.map (homOfLE hBC).op s = P.map (homOfLE hBC).op t) : s = t := by
  let U : Fin 2 → X.Opens := fun i => Fin.cases A (fun _ => B) i
  have hU0 : U 0 = A := rfl
  have hU1 : U 1 = B := rfl
  have hUC : ∀ i, U i ≤ C := by
    intro i; fin_cases i
    · exact (le_of_eq hU0).trans hAC
    · exact (le_of_eq hU1).trans hBC
  have hsup : iSup U = A ⊔ B := by
    rw [iSup_fin_succ 1 U, iSup_fin_one]
    rfl
  refine sheaf_sep_at hP U hUC (hcov.trans (le_of_eq hsup.symm)) (fun i => ?_)
  fin_cases i
  · have e : (homOfLE (hUC 0)).op = (homOfLE hAC).op := Subsingleton.elim _ _
    rw [e]; exact hA
  · have e : (homOfLE (hUC 1)).op = (homOfLE hBC).op := Subsingleton.elim _ _
    rw [e]; exact hB

/-- Gluing two sections which agree on the intersection, over a cover by two opens. -/
lemma glue_pair_of_sheaf {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (hP : TopCat.Presheaf.IsSheaf P) {A B C : X.Opens}
    (hAC : A ≤ C) (hBC : B ≤ C)
    (hcov : C ≤ A ⊔ B) (u : P.obj (op A)) (u' : P.obj (op B))
    (hcompat : P.map (Opens.infLELeft A B).op u = P.map (Opens.infLERight A B).op u') :
    ∃ y : P.obj (op C), P.map (homOfLE hAC).op y = u ∧ P.map (homOfLE hBC).op y = u' := by
  classical
  let U : Fin 2 → X.Opens := fun i => Fin.cases A (fun _ => B) i
  let sf : ∀ i, P.obj (op (U i)) := fun i => Fin.cases u (fun _ => u') i
  have hU0 : U 0 = A := rfl
  have hU1 : U 1 = B := rfl
  have hUC : ∀ i, U i ≤ C := by
    intro i; fin_cases i
    · exact (le_of_eq hU0).trans hAC
    · exact (le_of_eq hU1).trans hBC
  have hsup : iSup U = A ⊔ B := by
    rw [iSup_fin_succ 1 U, iSup_fin_one]
    rfl
  have hc : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    fin_cases i <;> fin_cases j
    · show P.map (Opens.infLELeft A A).op u = P.map (Opens.infLERight A A).op u
      congr 1
    · show P.map (Opens.infLELeft A B).op u = P.map (Opens.infLERight A B).op u'
      exact hcompat
    · show P.map (Opens.infLELeft B A).op u' = P.map (Opens.infLERight B A).op u
      exact (res_inf_comm' (P := P) (A := A) (B := B) u').symm.trans
        (((congrArg (fun z => resEq P (inf_comm A B) z) hcompat).symm).trans
          (res_inf_comm (P := P) (A := A) (B := B) u))
    · show P.map (Opens.infLELeft B B).op u' = P.map (Opens.infLERight B B).op u'
      congr 1
  obtain ⟨y, hy⟩ := sheaf_glue_at hP U hUC (hcov.trans (le_of_eq hsup.symm)) sf hc
  refine ⟨y, ?_, ?_⟩
  · have h := hy 0
    rw [show (homOfLE (hUC 0)).op = (homOfLE hAC).op from Subsingleton.elim _ _] at h
    dsimp only [sf] at h
    exact h
  · have h := hy 1
    rw [show (homOfLE (hUC 1)).op = (homOfLE hBC).op from Subsingleton.elim _ _] at h
    dsimp only [sf] at h
    exact h

/-! ### The two-open gluing step of the dévissage -/

/-- If two opens `A, B` cover `C ⊆ V`, if `u : K n (A)` and `u' : K n (B)` both map to the
restriction of a cycle `x : K (n+1) (C)`, and if the sheaf of `n`-cycles has surjective
restriction maps on `V`, then `x` is a coboundary over `C`. -/
lemma flasque_glue_two_aux
    (K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (d : ∀ n : ℕ, K n ⟶ K (n+1)) (V : X.Opens) (n : ℕ)
    (hZF : CyclesFlasque K d V n)
    (hshn : TopCat.Presheaf.IsSheaf (K n)) (hshn1 : TopCat.Presheaf.IsSheaf (K (n+1)))
    (A B C : X.Opens) (hAC : A ≤ C) (hBC : B ≤ C) (hcov : C ≤ A ⊔ B) (hCV : C ≤ V)
    (x : (K (n+1)).obj (op C)) (hx : (d (n+1)).app (op C) x = 0)
    (u : (K n).obj (op A)) (hu : (d n).app (op A) u = (K (n+1)).map (homOfLE hAC).op x)
    (u' : (K n).obj (op B)) (hu' : (d n).app (op B) u' = (K (n+1)).map (homOfLE hBC).op x) :
    ∃ y : (K n).obj (op C), (d n).app (op C) y = x := by
  -- the discrepancy of the two local primitives is a cycle over `A ⊓ B`
  let z : (K n).obj (op (A ⊓ B)) := (K n).map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op u
      - (K n).map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op u'
  have hz : (d n).app (op (A ⊓ B)) z = 0 := by
    dsimp only [z]
    rw [map_sub, d_naturality, d_naturality, hu, hu', res_trans, res_trans]
    rw [Subsingleton.elim ((inf_le_left : A ⊓ B ≤ A).trans hAC)
      ((inf_le_right : A ⊓ B ≤ B).trans hBC), sub_self]
  -- extend it to a cycle over `B`
  obtain ⟨w, hw0, hw1⟩ :=
    hZF (W' := A ⊓ B) (W := B) (h := inf_le_right) (hBC.trans hCV) z hz
  -- correct the second primitive and glue
  have hcompat : (K n).map (Opens.infLELeft A B).op u
      = (K n).map (Opens.infLERight A B).op (u' + w) := by
    show (K n).map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op u
      = (K n).map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op (u' + w)
    rw [map_add, hw1]
    dsimp only [z]
    abel
  obtain ⟨y, hy1, hy2⟩ := glue_pair_of_sheaf hshn hAC hBC hcov u (u' + w) hcompat
  refine ⟨y, ?_⟩
  have hw' : (d n).app (op B) (u' + w) = (K (n+1)).map (homOfLE hBC).op x := by
    rw [map_add, hu', hw0, add_zero]
  refine sheaf_sep_pair hshn1 hAC hBC hcov ?_ ?_
  · rw [← d_naturality d n hAC y, hy1, hu]
  · rw [← d_naturality d n hBC y, hy2, hw']

/-! ### The induction -/

/-- **The inductive step for the flasqueness of the sheaf of cycles.**  If every cocycle of
`K (n+1)` over an open `W ≤ V` is a coboundary over `W`, then the sheaf of `(n+1)`-cycles has
surjective restriction maps between opens contained in `V`: a cycle over `W'` is a coboundary
over `W'`, and a primitive extends to `W` by flasqueness of `K n`. -/
lemma cyclesFlasque_succ
    (K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (d : ∀ n : ℕ, K n ⟶ K (n+1))
    (hcomp : ∀ n : ℕ, CategoryStruct.comp (d n) (d (n+1)) = 0)
    (V : X.Opens) (n : ℕ)
    (hP : ∀ (W : X.Opens), W ≤ V → ∀ x : (K (n+1)).obj (op W),
      (d (n+1)).app (op W) x = 0 →
      ∃ y : (K n).obj (op W), (d n).app (op W) y = x)
    (hfl : TopCat.Presheaf.IsFlasque (K n)) :
    CyclesFlasque K d V (n+1) := by
  intro W' W h hWV z hz
  have hW'V : W' ≤ V := h.trans hWV
  obtain ⟨y, hy⟩ := hP W' hW'V z hz
  have hsurj : Function.Surjective (fun x : (K n).obj (op W) => (K n).map (homOfLE h).op x) :=
    (AddCommGrpCat.epi_iff_surjective ((K n).map (homOfLE h).op)).mp
      (hfl.epi (homOfLE h).op)
  obtain ⟨y', hy'⟩ := hsurj y
  have hy'' : (K n).map (homOfLE h).op y' = y := hy'
  refine ⟨(d n).app (op W) y', ?_, ?_⟩
  · have h1 := congrArg (fun (φ : K n ⟶ K (n+2)) => φ.app (op W) y') (hcomp n)
    simpa using h1
  · rw [← d_naturality d n h y', hy'', hy]

/-- **Exactness of the sections, given the two-open gluing step.**  If every cocycle of
`K (n+1)` over `W ≤ V` is a coboundary on the members of a finite cover of `W`, and if the
flasqueness of the sheaf of `n`-cycles allows to correct two local primitives against each
other over a union of two opens, then every cocycle of `K (n+1)` over `W ≤ V` is a coboundary
over `W`. -/
lemma exactAt_of_cyclesFlasque
    (K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (d : ∀ n : ℕ, K n ⟶ K (n+1)) (V : X.Opens) (n : ℕ)
    (hshn : TopCat.Presheaf.IsSheaf (K n)) (hshn1 : TopCat.Presheaf.IsSheaf (K (n+1)))
    (hglue : ∀ (A B C : X.Opens) (hAC : A ≤ C) (hBC : B ≤ C) (hcov : C ≤ A ⊔ B) (hCV : C ≤ V)
      (x : (K (n+1)).obj (op C)) (hx : (d (n+1)).app (op C) x = 0)
      (u : (K n).obj (op A))
      (hu : (d n).app (op A) u = (K (n+1)).map (homOfLE hAC).op x)
      (u' : (K n).obj (op B))
      (hu' : (d n).app (op B) u' = (K (n+1)).map (homOfLE hBC).op x),
      ∃ y : (K n).obj (op C), (d n).app (op C) y = x)
    (hlocal : ∀ (W : X.Opens), W ≤ V → ∀ x : (K (n+1)).obj (op W),
      (d (n+1)).app (op W) x = 0 →
      ∃ (m : ℕ) (W' : Fin m → X.Opens) (hW' : ∀ i, W' i ≤ W), iSup W' = W ∧
        ∀ i : Fin m, ∃ y : (K n).obj (op (W' i)),
          (d n).app (op (W' i)) y = (K (n+1)).map (homOfLE (hW' i)).op x) :
    ∀ (W : X.Opens), W ≤ V → ∀ x : (K (n+1)).obj (op W),
      (d (n+1)).app (op W) x = 0 →
      ∃ y : (K n).obj (op W), (d n).app (op W) y = x := by
  -- the induction on the number of members of the cover
  have aux : ∀ (m : ℕ) (A : X.Opens) (W' : Fin m → X.Opens) (hW' : ∀ i, W' i ≤ A)
      (hiSup : iSup W' = A) (hAV : A ≤ V)
      (x : (K (n+1)).obj (op A)) (hx : (d (n+1)).app (op A) x = 0)
      (y : ∀ i, (K n).obj (op (W' i)))
      (hy : ∀ i, (d n).app (op (W' i)) (y i) = (K (n+1)).map (homOfLE (hW' i)).op x),
      ∃ y₀ : (K n).obj (op A), (d n).app (op A) y₀ = x := by
    intro m
    induction m with
    | zero =>
      intro A W' hW' hiSup hAV x hx y hy
      haveI : Subsingleton ((K (n+1)).obj (op A)) :=
        subsingleton_obj_of_isSheaf_of_iSup_eq hshn1 W' hiSup
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩
    | succ m ih =>
      intro A W' hW' hiSup hAV x hx y hy
      let A' : X.Opens := ⨆ i : Fin m, W' i.castSucc
      have hA'A : A' ≤ A := iSup_le (fun i : Fin m => hW' i.castSucc)
      have hA'V : A' ≤ V := hA'A.trans hAV
      have hW'' : ∀ i : Fin m, W' i.castSucc ≤ A' :=
        fun i => le_iSup (fun j : Fin m => W' j.castSucc) i
      have hx' : (d (n+1)).app (op A') ((K (n+1)).map (homOfLE hA'A).op x) = 0 := by
        rw [d_naturality, hx, map_zero]
      have hy'' : ∀ i : Fin m, (d n).app (op (W' i.castSucc)) (y i.castSucc) =
          (K (n+1)).map (homOfLE (hW'' i)).op ((K (n+1)).map (homOfLE hA'A).op x) := by
        intro i
        rw [hy i.castSucc]
        have e : (K (n+1)).map (homOfLE (hW'' i)).op ((K (n+1)).map (homOfLE hA'A).op x)
            = (K (n+1)).map (homOfLE (hW' i.castSucc)).op x := by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          congr 1
        rw [e]
      obtain ⟨y', hy'⟩ := ih A' (fun i : Fin m => W' i.castSucc) hW'' rfl hA'V
        ((K (n+1)).map (homOfLE hA'A).op x) hx' (fun i => y i.castSucc) hy''
      have hAB : A' ⊔ W' (Fin.last m) = A := (iSup_fin_succ m W').symm.trans hiSup
      exact hglue A' (W' (Fin.last m)) A hA'A (hW' (Fin.last m)) (le_of_eq hAB.symm) hAV
        x hx y' hy' (y (Fin.last m)) (hy (Fin.last m))
  intro W hWV x hx
  obtain ⟨m, W', hW', hiSup, hlift⟩ := hlocal W hWV x hx
  choose y hy using hlift
  cases m with
  | zero =>
    haveI : Subsingleton ((K (n+1)).obj (op W)) :=
      subsingleton_obj_of_isSheaf_of_iSup_eq hshn1 W' hiSup
    exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩
  | succ m =>
    exact aux (m+1) W W' hW' hiSup hWV x hx y hy

/-! ### The theorem -/

theorem cechTrivAt_of_flasque_terms {X : AlgebraicGeometry.Scheme.{u}} (V : X.Opens)
    (K : ℕ → CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (d : ∀ n : ℕ, K n ⟶ K (n+1))
    (hcomp : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (d n) (d (n+1)) = 0)
    (F : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (aug : F ⟶ K 0)
    (hF : TopCat.Presheaf.IsFlasque F)
    (hzero : CategoryTheory.CategoryStruct.comp aug (d 0) = 0)
    (hexact0 : ∀ (W : X.Opens), W ≤ V → ∀ x : (K 0).obj (Opposite.op W),
      ((d 0).app (Opposite.op W) x = 0 ↔
        ∃ y : (F.obj (Opposite.op W)), (aug.app (Opposite.op W)) y = x))
    (hsh : ∀ n : ℕ, TopCat.Presheaf.IsSheaf (K n))
    (hfl : ∀ n : ℕ, TopCat.Presheaf.IsFlasque (K n))
    (hmono : ∀ W : X.Opens, W ≤ V →
      Function.Injective (fun x : (F.obj (Opposite.op W)) => (aug.app (Opposite.op W)) x))
    (hlocal : ∀ (n : ℕ) (W : X.Opens), W ≤ V → ∀ x : (K (n+1)).obj (Opposite.op W),
      (d (n+1)).app (Opposite.op W) x = 0 →
      ∃ (m : ℕ) (W' : Fin m → X.Opens) (hW' : ∀ i, W' i ≤ W), iSup W' = W ∧
        ∀ i : Fin m, ∃ y : (K n).obj (Opposite.op (W' i)),
          (d n).app (Opposite.op (W' i)) y =
            (K (n+1)).map (CategoryTheory.homOfLE (hW' i)).op x) :
    ∀ (n : ℕ) (W : X.Opens), W ≤ V → ∀ x : (K (n+1)).obj (Opposite.op W),
      (d (n+1)).app (Opposite.op W) x = 0 →
      ∃ y : (K n).obj (Opposite.op W), (d n).app (Opposite.op W) y = x := by
  -- the flasqueness of the sheaves of cycles, by induction on the degree
  have cycles : ∀ n : ℕ, CyclesFlasque K d V n := by
    intro n
    induction n with
    | zero => exact cyclesFlasque_zero_aux K d F aug V hF hzero hexact0
    | succ n ih =>
      exact cyclesFlasque_succ K d hcomp V n
        (exactAt_of_cyclesFlasque K d V n (hsh n) (hsh (n+1))
          (flasque_glue_two_aux K d V n ih (hsh n) (hsh (n+1))) (hlocal n)) (hfl n)
  intro n W hWV x hx
  exact exactAt_of_cyclesFlasque K d V n (hsh n) (hsh (n+1))
    (flasque_glue_two_aux K d V n (cycles n) (hsh n) (hsh (n+1))) (hlocal n) W hWV x hx

end Work.DSF1.Sheaf
