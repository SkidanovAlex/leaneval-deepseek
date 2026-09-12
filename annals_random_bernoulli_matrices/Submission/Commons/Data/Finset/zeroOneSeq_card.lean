import Mathlib.Data.Fintype.BigOperators

namespace Commons.Data.Finset

theorem zeroOneSeq_card (m : ℕ) :
    ((Finset.univ : Finset (Fin m → Fin 2)).image
        (fun b : Fin m → Fin 2 => fun i : Fin m => ((b i).val : ℤ))).card = 2 ^ m := by
  classical
  have hinj : Function.Injective (fun b : Fin m → Fin 2 => fun i : Fin m => ((b i).val : ℤ)) := by
    intro b c h
    funext i
    apply Fin.ext
    exact Int.ofNat.inj (congrFun h i)
  calc
    ((Finset.univ : Finset (Fin m → Fin 2)).image
        (fun b : Fin m → Fin 2 => fun i : Fin m => ((b i).val : ℤ))).card
        = (Finset.univ : Finset (Fin m → Fin 2)).card :=
          Finset.card_image_of_injective _ hinj
    _ = Fintype.card (Fin m → Fin 2) := Finset.card_univ
    _ = 2 ^ m := by simp

end Commons.Data.Finset