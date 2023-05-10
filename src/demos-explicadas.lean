import incidence_geometry

open incidence_geometry

/-- 
  Dos líneas distintas tienen como mucho un punto en común. 
-/
lemma disctinct_lines_one_common_point {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∀ l m : Line, l ≠ m → (∃! A : Point, is_common_point A l m) ∨ (¬ have_common_point Point l m) := 
begin
  /- El estado táctico inicial incluye los parámetros del lema. En este caso los tipos Point y Line 
     e ig, la instancia de la clase incidence_geometry. Esta instancia representa el hecho de que 
     los tipos Point y Line cumplen los axiomas de la geometría de incidencia.

     La meta se corresponde con el enunciado del lema, es decir lo que queremos demostrar.
  -/
  intros l m, 
  /- La aplicación de la táctica intros introduce las hipótesis l y m. 
     Es decir, saca el cuantificador universal de la meta e introduce las variables cuantificadas 
     en el estado táctico, pasando a tener ahora dos nuevos términos l y m, de tipo Line.
     La nueva meta es l ≠ m → (∃! (A : Point), is_common_point A l m) ∨ ¬have_common_point Point l m

     Esto es equivalente a cuando en una demostración clásica decimos en lenguaje natural "Sean l y m dos líneas cualesquiera".
  -/
  contrapose,
  /- La táctica contrapose permite realizar una demostración por contraposición. Es decir, si nuestra meta es de la forma A → B, 
     la reemplaza por ¬B → ¬A.

     En este caso la meta resultante es ¬((∃! (A : Point), is_common_point A l m) ∨ ¬have_common_point Point l m) → ¬l ≠ m
  -/
  push_neg,
  /- La táctica push_neg utiliza equivalencias lógicas para "empujar" las negaciones dentro de la fórmula. En este caso, 
     al no haber especificado una hipótesis concreta, se aplica sobre la meta.

     En la primera parte de la implicación se aplica una ley de De Morgan para introducir la negación dentro de una disjunción, 
     convirtiéndola en una conjunción de negaciones. En la segunda, negar una desigualdad equivale a una igualdad.

     Por tanto la meta resultante es (¬∃! (A : Point), is_common_point A l m) ∧ have_common_point Point l m → l = m

     Es interesante notar que push_neg no consigue "empujar" la negación todo lo que podríamos desear. 
     
     Esto es así porque no está reescribiendo las definiciones previas y de ∃!. 
     Esto lo tendremos que hacer manualmente, como se verá enseguida.
  -/
  rintro ⟨not_unique, hlm⟩,
  /- La táctica rintro funciona como intro, en este caso aplicada para asumir la hipótesis de la implicación que queremos demostrar.
     La variante rintro nos permite entrar en definiciones recursivas, en este caso en la del operador ∧, y mediante el uso de los 
     paréntesis ⟨⟩ introducir los dos lados de la conjunción como hipótesis separadas. 

     Por tanto después de aplicar esta táctica obtendremos dos hipótesis adicionales:
        not_unique: ¬∃! (A : Point), is_common_point A l m
        hlm: have_common_point Point l m
     y la meta resultante es el segundo lado de la implicación, es decir l = m.
  -/
  rw exists_unique at not_unique,
  /- La táctica rw (abreviación de rewrite) nos permite reescribir ocurrencias de fórmulas utilizando definiciones o lemas de la forma A ↔ B.
     Al escribir at indicamos dónde queremos realizar dicha reescritura, en este caso en la hipótesis not_unique.#check

     En este caso utilizamos la definición de ∃!, con lo que la hipótesis not_unique resulta:
       ¬∃ (x : Point), is_common_point x l m ∧ ∀ (y : Point), is_common_point y l m → y = x
  -/
  push_neg at not_unique,
  /- Como comentábamos antes, ahora que hemos reescrito la definición de ∃! podemos seguir "empujando" la negación en la hipótesis not_unique,
     obteniendo ∀ (x : Point), is_common_point x l m → (∃ (y : Point), is_common_point y l m ∧ y ≠ x)
  -/
  cases hlm with A hA,
  /- La táctica cases nos permite, entre otras cosas, dada una hipótesis de existencia, obtener un término del tipo cuantificado por el existe y la 
     correspondiente hipótesis particularizada para el nuevo término.
     
     En nuestro caso tenemos la hipótesis 
       hlm: have_common_point Point l m
     
     y la definición de have_common_point Point l m es 
       have_common_point Point l m := ∃ A : Point, is_common_point A l m
    
     Por tanto al aplicar la táctica, la hipótesis hlm se convierte en dos nuevas hipótesis
      A: Point
      hA: is_common_point A l m
  -/
  rcases not_unique A hA with ⟨B, ⟨hB, hAB⟩⟩,
  /- Recordemos que en el estado táctico actual tenemos la hipótesis 
       not_unique: ∀ (x : Point), is_common_point x l m → (∃ (y : Point), is_common_point y l m ∧ y ≠ x)
  En esta línea están ocurriendo distintas cosas. 
       - Se está aplicando la táctica rcases al término not_unique A hA.
         En Lean los cuantificadores universales y las implicaciones pueden tratarse como funciones:
         - Al pasar el primer argumento A estamos particularizando la cuantificación sobre el punto x, proporcionando el 
           término A: Point que tenemos entre nuestras hipótesis. Por tanto el término not_unique A es igual a 
             is_common_point A l m → (∃ (y : Point), is_common_point y l m ∧ y ≠ A)
         - Ahora podemos observar que tenemos entre nuestras hipótesis la condición de esta implicación, hA: is_common_point A l m
           Al pasar este término como argumento obtenemos la conclusión de la implicación, y por tanto el término not_unique A hA es igual a
             ∃ (y : Point), is_common_point y l m ∧ y ≠ x
       - La aplicación de la táctica rcases nos permite, como anteriormente, obtener un término concreto del cuantificador existencial y además 
         profundizar en la definición recursiva del ∧, generando así dos hipótesis separadas. Obtenemos por tanto las nuevas hipótesis:
           B: Point
           hB: is_common_point B l m
           hAB: B ≠ A
  -/
  rw ne_comm at hAB,
  /- Para tener la hipótesis hAB: B ≠ A en el mismo orden que el utilizado en los axiomas y poder utilizarlos correctamente, 
     reescribimos la hipótesis hAB utilizando la propiedad conmutativa de la desigualdad, obteniendo así la hipóteis 
    hAB: A ≠ B
  -/
  exact unique_of_exists_unique (ig.I1 hAB) ⟨hA.left,hB.left⟩ ⟨hA.right,hB.right⟩,
  /-
    La táctica exact se utiliza para concluir la demostración proporcionando un término igual a la meta.
    Recordemos que la meta actual es l = m.

    Analicemos entonces el término que estamos proporcionando a la táctica.

    El lema unique_of_exists_unique, definido en la librería estándar de lean, sirve para extrer la parte de unicidad del 
    cuantificador ∃!. Dados tres argumentos, una fórmula de la forma ∃! x, px; y dos fórmulas para términos que cumplan la hipótesis p, 
    devuelve la fórmula que aserta la igualdad entre estos términos.

    Como primer argumento le estamos pasando el primer axioma de incidencia, particularizado con la hipóteis hAB : A ≠ B. 
    Es decir ig.I1 hAB es igual a ∃! l : Line, A ~ l ∧ B ~ l
    Ahora queremos pasar otros dos argumentos con tipos A ~ l ∧ B ~ l y A ~ m ∧ B ~ m, para obtener la igualdad l = m
    Para esto tenemos que recombinar las hipótesis hA y hB, que dicen que A y B están tanto en l como en m, respectivamente.

    hA.left es igual a A ~ l, hB.left a B ~ l, y mediante los paréntesis ⟨⟩ combinamos estos términos en la conjunción
    ⟨hA.left,hB.left⟩ es igual a A ~ l ∧ B ~ l.

    El uso de los paréntesis nos permite construir una conjunción sin tener que especificar esplícitamente que queremos construir una 
    conjunción, pero el sistema de tipos de Lean permite inferir que el término esperado es una conjunción.

    Análogamente para el segundo argumento.
  -/
end